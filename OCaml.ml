(* Interprete di un semplice linguaggio funzionale.*)

type variable = string ;;

type constant = Int of int | Bool of bool ;;

type operator = Plus | Minus | Times | Div | LessThan | LessThanEq ;;

(* Le espressioni. *)

type exp =
  | Constant_e of constant
  | Op_e of exp * operator * exp
  | Var_e of variable
  | If_e of exp * exp * exp
  | Fun_e of variable * exp
  | FunCall_e of exp * exp
  | Let_e of variable * exp * exp
  | Letrec_e of variable * exp * exp
  (* Estensione delle espressioni *)
  | ETree of tree (* gli alberi sono anche espressioni *)
  | ApplyOver of exp * exp (* applicazione di funzione ai nodi *)
  | Update of (variable list) * exp * exp (* aggiornamento di un nodo *)
  | Select of (variable list) * exp * exp (* selezione condizionale di un nodo *)
    and tree = Empty (* albero vuoto *)
    | Node of variable * exp * tree * tree (* albero binario *)
;;

(* funzioni del run-time *)

(* Controllo per valori *)

let rec is_value (e:exp) : bool =
  match e with
    | Constant_e _ -> true
    | Fun_e (_,_) -> true
    | (
        Op_e (_,_,_)
       | Var_e _
       | If_e (_,_,_)
       | FunCall_e (_,_)
       | Let_e (_,_,_)
       | Letrec_e (_,_,_)
       | ETree _
       | ApplyOver (_,_)
       | Update (_,_,_)
       | Select (_,_,_)
    ) -> false
;;

(* casi possibili di run-time exception *)

exception UnboundVariable of variable ;;
exception BadApplication of exp ;;
exception BadIf of exp ;;
exception BadOp of exp * operator * exp ;;

(* decodifica delle operazioni di base *)

let apply_op v1 op v2 =
  match v1, op, v2 with
    | Constant_e (Int i), Plus, Constant_e (Int j) ->
        Constant_e (Int (i+j))
    | Constant_e (Int i), Minus, Constant_e (Int j) ->
        Constant_e (Int (i-j))
    | Constant_e (Int i), Times, Constant_e (Int j) ->
        Constant_e (Int (i*j))
    | Constant_e (Int i), Div, Constant_e (Int j) ->
        Constant_e (Int (i/j))
    | Constant_e (Int i), LessThan, Constant_e (Int j) ->
        Constant_e (Bool (i<j))
    | Constant_e (Int i), LessThanEq, Constant_e (Int j) ->
        Constant_e (Bool (i<=j))
    | _, _, _ -> raise (BadOp (v1,op,v2))
;;

(* Funzione di sostituzione *)
(* Notare uso di una funzione ricorsiva ausiliaria *)

(* let x = v in e *)
let substitute (v:exp) (x:variable) (e:exp) : exp =
  let rec subst (e:exp) : exp =
    match e with
    | Var_e y -> if x = y then v else e
    | Constant_e _ -> e
    | Op_e (e1,op,e2) -> Op_e(subst e1,op,subst e2)
    | If_e (e1,e2,e3) -> If_e(subst e1,subst e2,subst e3)
    | FunCall_e (e1,e2) -> FunCall_e(subst e1,subst e2)
    | Fun_e (y,e1) -> if x = y then e else Fun_e (y, subst e1)
    | Let_e (y,e1,e2) ->
        Let_e (y, subst e1, if x = y then e2 else subst e2)
    | Letrec_e (y,e1,e2) ->
        if x = y then Letrec_e (y,e1,e2) else Letrec_e (y,subst e1,subst e2)
    (* ESTENSIONE *)
    | ETree t -> (
        match t with
        | Empty -> ETree(Empty)
        | Node(y, e, lt, rt) ->
            (match subst (ETree lt) with
                | ETree lts ->
                    (match subst (ETree rt) with
                        | ETree rts -> ETree(Node(y, subst e, lts, rts))
                        | v2 -> raise(BadApplication v2)
                    )
                | v1 -> raise(BadApplication v1)
            )
        )
    | ApplyOver (exf, ext) -> ApplyOver(subst exf, subst ext)
    | Update (idl, exf, ext) -> Update (idl, subst exf, subst ext)
    | Select (idl, exf, ext) -> Select (idl, subst exf, subst ext)
  in
    subst e
;;


(* Ciclo dell'interprete *)
(* Notare uso di una chiamata ricorsiva tramite parametri higher-order *)
(* Notare uso della sostituzione per fare unwind della ricorsione *)

let eval_body (eval_loop:exp->exp) (e:exp) : exp =
  match e with
    | Constant_e c -> Constant_e c
    | Fun_e (x,e) -> Fun_e (x,e)
    | Op_e (e1,op,e2) ->
        let v1 = eval_loop e1 in
        let v2 = eval_loop e2 in
          apply_op v1 op v2
    | If_e (e1,e2,e3) ->
          (match eval_loop e1 with
             | Constant_e (Bool true) -> eval_loop e2
             | Constant_e (Bool false) -> eval_loop e3
             | v1 -> raise (BadIf v1))
    | Let_e (x,e1,e2) -> eval_loop (substitute (eval_loop e1) x e2)
    | FunCall_e (e1,e2) ->
        (match eval_loop e1 with
           | Fun_e (x,e) -> eval_loop (substitute (eval_loop e2) x e)
           | v1 -> raise (BadApplication v1))
    | Var_e x -> raise (UnboundVariable x)
    | Letrec_e (x,e1,e2) ->
        let e1_unwind = substitute (Letrec_e (x,e1,Var_e x)) x e1 in
          eval_loop (Let_e (x,e1_unwind,e2))
    (* ESTENSIONE *)
    | ETree t -> (
        match t with
        | Empty -> ETree (Empty)
        | Node(y, et, lt, rt) ->
            (match eval_loop ( ETree(lt) ) with
                | ETree lte ->
                    (match eval_loop ( ETree(rt) ) with
                        | ETree rte -> ETree(Node(y, eval_loop et, lte, rte))
                        | v2 -> raise(BadApplication v2)
                    )
                | v1 -> raise(BadApplication v1)
            )
        )
    | ApplyOver(exf, ext) ->
        (match eval_loop exf with
            | Fun_e (p, ef) -> (
                match eval_loop ext with
                | ETree(Empty) -> ETree(Empty)
                | ETree Node(idl, en, lt, rt) ->
                    (match eval_loop (ApplyOver(Fun_e(p, ef), ( ETree(lt) ))) with
                    | ETree lte -> (
                        match eval_loop (ApplyOver(Fun_e(p, ef), ( ETree(rt) ))) with
                            | ETree rte ->
                                ETree(Node(
                                    idl,
                                    eval_loop (FunCall_e(Fun_e(p, ef), eval_loop en)),
                                    lte,
                                    rte
                                 ))
                            | v4 -> raise(BadApplication v4)
                        )
                    | v3 -> raise(BadApplication v3)
                    )
                | v2 -> raise(BadApplication v2)
              )
            | v1 -> raise(BadApplication v1)
        )
    | Update(idl, exf, ext) ->
      (match eval_loop exf with
        | Fun_e (p, ef) ->
          (match eval_loop ext with
            | ETree(Empty) -> ETree(Empty)
            | ETree Node(idln, en, lt, rt) ->
              (match idl with
                | [] -> ETree(Node(idln, en, lt, rt))
                | h::[] -> (if h = idln then ETree(Node(
                                    idln,
                                    eval_loop (FunCall_e(Fun_e(p, ef), (eval_loop en))),
                                    lt,
                                    rt
                                  ))
                  else ETree(Node(idln, en, lt, rt)))
                | h::t -> (if h = idln then
                        (match eval_loop (Update(t, Fun_e (p, ef), ETree(lt))) with
                            | ETree lte ->
                                (match eval_loop (Update(t, Fun_e (p, ef), ETree(rt))) with
                                    | ETree rte ->
                                       ETree(Node(
                                          idln,
                                          en,
                                          lte,
                                          rte
                                       ))
                                    | v4 -> raise(BadApplication v4)
                                )
                            | v3 -> raise(BadApplication v3)
                        )
                  else ETree(Node(idln, en, lt, rt)))
            )
            | v2 -> raise(BadApplication v2)
          )
        | v1 -> raise(BadApplication v1)
      )
    | Select(idl, exf, ext) -> (
        match eval_loop exf with
            | Fun_e (p, ef) -> (
                match eval_loop ext with
                    | ETree(Empty) -> ETree(Empty)
                    | ETree Node(idt, en, lt, rt) ->
                        (
                            match idl with
                            | [] -> ETree(Empty)
                            | h::[] -> if h = idt then
                                    let ret = eval_loop (FunCall_e(Fun_e (p, ef), eval_loop en)) in
                                        (
                                            match ret with
                                            | Constant_e(Bool(t)) ->
                                                (
                                                    if t = true then ETree(Node(idt, en, lt, rt))
                                                    else ETree(Empty)
                                                )
                                            | v3 -> raise(BadApplication v3)
                                        )
                                else ETree(Empty)
                            | h::t -> if h = idt then
                                    let ret = eval_loop (FunCall_e(Fun_e (p, ef), eval_loop en)) in
                                        (
                                            match ret with
                                            | Constant_e(Bool(tr)) ->
                                                (
                                                    if tr = true then
                                                        (match eval_loop (Select(t, exf, ETree(lt))) with
                                                            | ETree(Empty) ->
                                                                (match eval_loop (Select(t, exf, ETree(rt))) with
                                                                    | ETree(Empty) -> ETree(Empty)
                                                                    | st -> st
                                                                )
                                                            | st -> st
                                                        )
                                                    else ETree(Empty)
                                                )
                                            | v3 -> raise(BadApplication v3)
                                        )
                                else ETree(Empty)
                        )
                    | v2 -> raise(BadApplication v2)
                )
            | v1 -> raise(BadApplication v1)
        )
;;

let rec eval e = eval_body eval e
;;

(* TEST *)

(* Definizione albero di prova *)
let albero = ETree(
    Node("a", Constant_e(Int(2)),
      Node("b", Op_e(Constant_e(Int(3)), Plus, Constant_e(Int(1))),
        Empty,
        Node("d", Constant_e(Int(6)),
          Node("f", Op_e(Constant_e(Int(4)), Times, Constant_e(Int(2))), Empty, Empty),
          Empty
        )
      ),
      Node("c", Constant_e(Int(3)),
        Empty,
        Node("e", Constant_e(Int(7)), Empty, Empty)
      )
    )
  );;
(*
Albero:      ("a",2)
             /     \
      ("b",3+1)   ("c",3)
         \         \
      ("d", 6)     ("e", 7)
        /
      ("f", 4*2)
*)

(* Funzione che triplica un numero *)
let triplica_body = Fun_e("x", 
    Op_e (Var_e "x", Times, Constant_e (Int 3)));;

(* Funzione per controllare disparità di un numero *)
(* Facciamo:    x <= 2*|x/2| <-- vero se e solo se è pari  *)
let ispari_body = Fun_e("x", Op_e (Var_e "x", LessThanEq, Op_e(Constant_e(Int 2), Times, Op_e(Var_e "x", Div, Constant_e(Int 2)) )));;

(* Valutazione di un albero: valuta le espressioni dei singoli nodi *)
eval albero;;

(* Test ApplyOver *)
eval (ApplyOver(triplica_body, albero));; (* Ritorna l'albero con tutte le espressioni triplicate *)
eval (ApplyOver(ispari_body, albero));; (* Ritorna l'albero con tutte le espressioni triplicate *)

(* Test Update *)
eval (Update(["a";"b";"d"], triplica_body, albero));; (* Triplica solo il nodo con espressione 6, avente cammino "a" "b" "d" *)
eval (Update(["a";"b";"c"], triplica_body, albero));; (* Non esiste nessun cammino con etichettatura "a" "b" "c", l'albero rimane invariato *)

(* Test Select *)
eval (Select(["a";"b";"d"], ispari_body, albero));; (* Seleziono il sotto albero avente radice il nodo con etichetta "d" *)
eval (Select(["a";"b";"z"], ispari_body, albero));; (* Non trova nessun cammino con etichettaura "a" "b" "z"*)



