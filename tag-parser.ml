#use "reader.ml";;
open Reader;;
(*#use "tag-parser.ml";;
open Tag_Parser;;*)
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
exception X_excp;;
(*
module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct
*)
module Tag_Parser = struct 

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
let isReserved str = List.fold_right (fun curr acc-> if(curr = str) then true else acc) reserved_word_list false;;

let rec pair_to_list f pair= match pair with
|Nil -> []
|Pair(x, Nil) -> [f x] (*proper list last elemnt*)
|Pair(x, Pair(y,rest)) -> (f x) :: (pair_to_list f (Pair(y, rest)))
|Pair(x, something) -> [f x] (*improper list last element, dont take the last element*)      
|_ -> raise X_syntax_error;;

let rec getOptinal pair = match pair with
|Nil -> ""          (*no parameters*)
|Pair(x, Nil) -> ""
|Pair(x, Symbol(sym)) -> sym (*has optional parameter- improper list*)
|Pair(x, Pair(y, rest)) -> getOptinal(Pair(y, rest))
|_-> raise X_syntax_error;;

let pull_string pair = pair_to_list 
(fun(x)-> match x with
|Symbol(x)-> x
|_ -> raise X_syntax_error) pair;;

let rec tag_pars sexpr = match sexpr with
| Pair(Symbol("lambda"), Pair(list_of_param, Pair(body, Nil)))-> body
|_-> raise X_syntax_error;;

(*et expendQuasy sexpr = match sexpr with 
|Pair(Symbol("unquote"), Pair (exp1, Nil)) -> exp1
|Pair(Symbol("unquote-splicing"), Pair (exp1, Nil)) -> raise X_syntax_error
|Symbol(str) -> Pair(Symbol("quote"), Pair(Symbol(str), Nil))
|Nil ->Pair (Symbol("quote"),Pair (Nil, Nil))
|Pair(Pair(Symbol("unquote-splicing"), Pair (exp1, Nil)),b) -> ((append ⟨sexpr⟩ 􏰀B􏰁)) exp1
|Pair(a,Pair(Symbol("unquote-splicing"), Pair (exp1, Nil))) -> Pair((expendQuasy a),exp1)
|Pair(a,b)-> Pair((expendQuasy a),(expendQuasy b))
|_ -> raise X_syntax_error;;
*)
let macro_expansion_and sexp = match sexp with 
|Nil -> Bool(true)
|Pair(expr,Nil) -> expr
|Pair(expr,rest) ->  Pair(Symbol("if"), Pair(expr, Pair(Pair (Symbol("and"),rest), Pair(Bool(false), Nil)))) 
|_ ->raise X_syntax_error;;
let macro_expansion_cond_rib rib cont = match rib with
|Pair(expr, Pair(Symbol("=>"), Pair(expf, Nil)))-> Pair(Symbol("let"),
Pair(Pair(Pair(Symbol("value"), Pair(expr, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(expf, Nil))), Nil)), Nil)), 
Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), cont))), Nil)))
|Pair(Symbol("else"), seq) -> Pair(Symbol("begin"), seq)
|Pair(test, dit) -> Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"),dit), cont))) 
|_-> rib ;; (*implicit else*)

let rec macro_expansion_cond ribs = match ribs with 
|Pair(rib, Nil) -> macro_expansion_cond_rib rib Nil
|Pair(rib, restRibs)-> let rest_ribs_expander = macro_expansion_cond restRibs in
 macro_expansion_cond_rib rib (Pair (rest_ribs_expander, Nil)) (*the last thing in the specific if*)
 |_-> raise X_syntax_error;; 


let rec get_params ribs = match ribs with 
|Pair( Pair(param, Pair(value, Nil)), Nil) -> Pair(param, Nil)    (*last rib*)
|Pair( Pair(param, Pair(value, Nil)), ribs)-> Pair(param, get_params ribs)
|_-> raise X_syntax_error ;; 

let rec get_values ribs = match ribs with 
|Pair( Pair(param, Pair(value, Nil)), Nil) -> Pair(value, Nil)    (*last rib*)
|Pair( Pair(param, Pair(value, Nil)), ribs)-> Pair(value, get_values ribs)
|_-> raise X_syntax_error ;; 

let macro_expansion_let sexpr_let = match sexpr_let with 
| Pair(Symbol("let"), Pair(Nil, Pair(body, Nil))) -> Pair(Pair(Symbol("lambda"), Pair(Nil , Pair(body, Nil))), Nil)
| Pair(Symbol("let"), Pair(ribs, Pair(body, Nil))) -> Pair(Pair(Symbol("lambda"), Pair(get_params ribs, Pair(body, Nil))), get_values ribs)
|_-> raise X_syntax_error;;

let macro_expansion_let_star sexpr = match sexpr with 
|Pair(Symbol("let*"), Pair(Nil, Pair(body, Nil))) -> Pair(Symbol("let"), Pair(Nil, Pair(body, Nil)))
|Pair(Symbol("let*"), Pair(Pair(rib, Nil), Pair(body, Nil))) -> 
Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(body, Nil))) 
|Pair(Symbol("let*"), Pair(Pair(rib, rest_ribs), Pair(body, Nil))) -> 
Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair(rest_ribs, Pair(body, Nil))), Nil))) 
|_-> raise X_syntax_error;;

let rec tag_parse sexpr = match sexpr with 
(*|Pair (Symbol("quasiquote"),Pair(sexp,Nil)) -> tag_parse (expendQuasy sexp)*)
| Pair(Symbol("and"),sexp) -> tag_parse (macro_expansion_and sexp)
| Pair(Symbol("let*"), _) -> tag_parse (macro_expansion_let_star sexpr)
| Pair(Symbol("let"), Pair(Nil, Pair(body, Nil))) -> tag_parse (macro_expansion_let sexpr)
| Pair(Symbol("let"), Pair(Pair(rib, ribs), Pair(body, Nil))) ->  tag_parse (macro_expansion_let sexpr)
| Pair(Symbol("cond"), ribs) -> tag_parse (macro_expansion_cond ribs)
| Pair(Symbol("begin"), Nil) -> Const(Void)
| Pair(Symbol("begin"), Pair(sexp, Nil)) -> tag_parse sexp 
| Pair(Symbol("begin"), list_of_exp) -> Seq(pair_to_list tag_parse list_of_exp)
| Pair(Symbol("or") , list_of_params) -> let exp_list = pair_to_list tag_parse list_of_params in Or(exp_list)
| Pair(Symbol("set!"), Pair(id, Pair (value,Nil))) -> Set((tag_parse id),(tag_parse value))
| Pair(Symbol("define"), Pair(nameVar , Pair(exp , Nil))) -> Def(tag_parse nameVar, tag_parse exp)
| Pair(Symbol("lambda"), Pair(Symbol(sym), Pair(body, Nil)))-> LambdaOpt([],sym, tag_parse body)
| Pair(Symbol("lambda"), Pair(list_of_param, Pair(body, Nil)))-> 
  let optional = getOptinal list_of_param in 
  if(optional = "") then LambdaSimple(pull_string list_of_param , tag_parse body)
  else LambdaOpt(pull_string list_of_param, optional, tag_parse body)
(*to check*)
| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
 If(tag_parse  test, tag_parse dit, tag_parse dif)
| Pair(Symbol("if"), Pair(test,Pair(dit, Nil))) -> let () = printf("if is god") in 
 If(tag_parse  test, tag_parse dit, Const(Void))
| Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x)) 
| Pair(closure, args_list)-> Applic((tag_parse closure), (pair_to_list tag_parse args_list))
| Symbol(x) ->  if(isReserved(x) = false) then Var(x)  else let () = printf("%s no") x in raise X_excp
| TagRef(x) -> Const(Sexpr(TagRef(x)))
| TaggedSexpr (st, Pair (Symbol "quote", Pair (x, Nil))) -> Const(Sexpr(TaggedSexpr(st, x)))
| TaggedSexpr (st,x) -> Const(Sexpr(TaggedSexpr(st, x)))
| Number(x) -> Const(Sexpr(Number(x)))
| Bool(x) -> Const(Sexpr(Bool(x)))
| Char(x) -> Const(Sexpr(Char(x)))
| String(x) -> Const(Sexpr(String(x)))
|_-> raise X_excp;;

let tag_parse_expression sexpr = tag_parse sexpr;;


let tag_parse_expressions sexpr = raise X_not_yet_implemented;;

  
end;; (* struct Tag_Parser *)
