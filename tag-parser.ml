#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
let isReserved str = List.fold_right (fun curr acc-> if(curr == str) then true else acc) reserved_word_list  false;;
(*pair to proper list*)
let rec pair_to_list f pair= match pair with
|Pair(x, Nil) -> []
|Pair(x, rest) -> (f x) :: (pair_to_list f rest)
|_ -> raise X_syntax_error;;

let rec isProper pair = match pair with
|Pair(x, Nil) -> true
|Pair(x, y) -> isProper(y)
|Pair(x,_) -> false (*improper list*)
|_-> raise X_syntax_error;; 

let pull_string pair = pair_to_list 
(fun(x)-> match x with
|Symbol(x)-> x
|_ -> raise X_syntax_error) pair;;

let tag_parse_expression sexpr = function  
(*| Pair(Symbol("let"), Pair(Nil, Pair(body, Nil))) ->
| Pair(Symbol("let"), Pair(Pair(rib, ribs), Pair(body, Nil))) -> *)

(*to check*)
(*| Pair(closure, args_list)-> Applic((tag_parse_expression closure), (pair_to_list tag_parse_expression args_list))

| Pair(Symbol("lambda"), Pair(list_of_param, Pair(body, Nil)))-> 
  if(isProper list_of_param) then LambdaSimple(pull_string list_of_param , tag_parse_expression body)
  else LambdaOpt(list_of_param, optional, tag_parse_expression body)
| Pair(Symbol("lambda"), Pair(Symbol(sym), Pair(body, Nil)))-> LambdaOpt([],sym, tag_parse_expression body)
*)
(*to check*)
(*| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
If(tag_parse_expression  test, tag_parse_expression dit, tag_parse_expression dif)
| Pair(Symbol("if"), Pair(test,Pair(dit, Nil))) ->
If(tag_parse_expression  test, tag_parse_expression dit, Const(Void))
| Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x)) 
| Symbol(x) -> if(isReserved(x) = false) then Var(Sexpr(Symbol(x))) 
| TagRef(x) -> Const(Sexpr(TagRef(x)))
| TaggedSexpr (st, Pair (Symbol "quote", Pair (x, Nil))) -> Const(Sexpr(TaggedSexpr(st, x)))
| TaggedSexpr (st,x) -> Const(Sexpr(TaggedSexpr(st, x)))
*)
(*unquoted sexspr *)
| Number(x) -> Const(Sexpr(Number(x)))
| Bool(x) -> Const(Sexpr(Bool(x)))
| Char(x) -> Const(Sexpr(Char(x)))
| String(x) -> Const(Sexpr(String(x)))


let tag_parse_expressions sexpr = raise X_not_yet_implemented;;

  
end;; (* struct Tag_Parser *)
