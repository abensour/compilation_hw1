
#use "reader.ml";;
open Reader;;

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
let isReserved str = List.fold_right (fun curr acc-> if(curr = str) then true else acc) reserved_word_list false;;

(*returns list from pair - if its improper doesn't return the last element*)
let rec pair_to_list f pair= match pair with
|Nil -> []
|Pair(x, Nil) -> [f x] (*proper list last elemnt*)
|Pair(x, Pair(y,rest)) -> (f x) :: (pair_to_list f (Pair(y, rest)))
|Pair(x, something) -> [f x] (*improper list last element, dont take the last element*)      
|_ -> raise X_syntax_error;;

let rec pair_to_pair f pair = match pair with
|Nil -> Nil
|Pair(x, Nil) -> Pair((f x),Nil)
|Pair(x,rest) -> Pair((f x),(pair_to_pair f rest))
|_ ->raise X_syntax_error;;

let rec pair_concate pairs add = match pairs with
|Nil -> add
|Pair(x, Nil) -> Pair(x,add)
|Pair(x,rest) -> Pair(x,(pair_concate rest add))
|_ ->raise X_syntax_error;;

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

let rec expendQuasy sexpr = match sexpr with 
|Pair(Symbol("unquote"), Pair (exp1, Nil)) -> exp1
|Pair(Symbol("unquote-splicing"), Pair (exp1, Nil)) -> raise X_syntax_error
|Symbol(str) -> Pair(Symbol("quote"), Pair(Symbol(str), Nil))
|Nil ->Pair (Symbol("quote"),Pair (Nil, Nil))
|Pair(Pair(Symbol("unquote-splicing"), Pair (exp1, Nil)),b) -> Pair(Symbol("append"),Pair(exp1,Pair((expendQuasy b),Nil)))
|Pair(a,Pair(Symbol("unquote-splicing"), Pair (exp1, Nil))) -> Pair(Symbol("cons"),Pair((expendQuasy a),Pair(exp1,Nil)))
|Pair(a,b)-> Pair(Symbol("cons"),Pair((expendQuasy a),Pair((expendQuasy b),Nil)))
|_ -> sexpr;;

let macro_expansion_and sexp = match sexp with 
|Nil -> Bool(true)
|Pair(expr,Nil) -> expr
|Pair(expr,rest) ->  Pair(Symbol("if"), Pair(expr, Pair(Pair (Symbol("and"),rest), Pair(Bool(false), Nil)))) 
|_ ->raise X_syntax_error;;

let macro_expansion_cond_rib rib cont = match rib, cont with
|Pair(expr, Pair(Symbol("=>"), Pair(expf, Nil))), Nil-> Pair (Symbol "let",
 Pair(Pair(Pair(Symbol "value", Pair(expr , Nil)), Pair(Pair (Symbol "f",
 Pair (Pair (Symbol "lambda", Pair (Nil, Pair (expf, Nil))), Nil)), Nil)), Pair(Pair (Symbol "if",
 Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), cont))),  Nil)))
|Pair(expr, Pair(Symbol("=>"), Pair(expf, Nil))), _-> Pair (Symbol "let",
 Pair(Pair(Pair (Symbol "value", Pair (expr, Nil)), Pair (Pair (Symbol "f",
 Pair (Pair (Symbol "lambda", Pair (Nil, Pair (expf, Nil))), Nil)), Pair (Pair (Symbol "rest",
 Pair (Pair (Symbol "lambda", Pair (Nil, cont)), Nil)),Nil))),
 Pair (Pair (Symbol "if", Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
 Pair (Pair (Symbol "rest", Nil), Nil)))),  Nil)))
|Pair(Symbol("else"), seq), _ -> Pair(Symbol("begin"), seq)
|Pair(test, dit), _ -> Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"),dit), cont))) 
|_, _-> rib ;; (*implicit else*)

let rec macro_expansion_cond ribs = match ribs with 
|Pair(rib, Nil) -> macro_expansion_cond_rib rib Nil
|Pair(rib, restRibs)-> let rest_ribs_expander = macro_expansion_cond restRibs in
 macro_expansion_cond_rib rib (Pair(rest_ribs_expander, Nil))
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
| Pair(Symbol("let"), Pair(Nil, body)) -> Pair(Pair(Symbol("lambda"), Pair(Nil , body)), Nil)
| Pair(Symbol("let"), Pair(ribs, body)) -> Pair(Pair(Symbol("lambda"), Pair(get_params ribs,body)), get_values ribs)
|_-> raise X_syntax_error;;

let macro_expansion_let_star sexpr = match sexpr with 
|Pair(Symbol("let*"), Pair(Nil, body)) -> Pair(Symbol("let"), Pair(Nil, body))
|Pair(Symbol("let*"), Pair(Pair(rib, Nil), body)) -> 
Pair(Symbol("let"), Pair(Pair(rib, Nil), body)) 
|Pair(Symbol("let*"), Pair(Pair(rib, rest_ribs), body)) -> 
Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair(rest_ribs, body)), Nil))) 
|_-> raise X_syntax_error;;

let rib_expand rib = match rib with 
|Pair(name,Pair(_,Nil)) -> Pair(name,Pair(Pair (Symbol("quote"), Pair(Symbol("whatever"), Nil)),Nil))
|_ -> raise X_syntax_error;;

let set_rib_expend rib = match rib with 
|Pair(name,Pair(func,Nil)) -> Pair (Symbol ("set!"), Pair (name, Pair (func, Nil)))
|_ -> raise X_syntax_error;;


let macro_expansion_letrec sexpr = match sexpr with 
|Pair(Symbol("letrec"), Pair(ribs, body)) -> let ribsLet = pair_to_pair rib_expand ribs
 in let ribsSet = pair_to_pair set_rib_expend ribs in
 Pair (Symbol("let"),Pair(ribsLet, (pair_concate ribsSet body)))
|_ -> raise X_syntax_error;;

let macro_expansion_MIT_define sexpr = match sexpr with 
| Pair(Symbol("define"), Pair(Pair(name, args), body)) -> 
Pair(Symbol("define"), Pair(name, Pair(Pair(Symbol("lambda"), Pair(args, body)), Nil)))
|_-> raise X_syntax_error;;

let duplicate_arg arg_str args_list = 
let counter_arg = List.fold_right (fun curr acc -> if(curr = arg_str) then acc+ 1 else acc) args_list 0
in if(counter_arg > 1) then true else false;; 

let check_if_legal_args list_of_args = 
let args = pull_string list_of_args in 
let optional = getOptinal list_of_args in 
let args = optional :: args in 
let check = List.fold_right (fun curr acc-> if((isReserved curr) || (duplicate_arg curr args)) then false else acc ) args true 
in check;; 

let rec tag_parse sexpr =  

let rec get_body_exprs body = match body with 
|Pair(sexpr, Nil) -> [tag_parse sexpr] (*one expr in the body*)
|Pair(sexpr, rest) -> (tag_parse sexpr) :: (get_body_exprs rest) (*seq*)
|_-> raise X_syntax_error  in

let tag_parse_body body = 
let exprs = get_body_exprs body in 
match exprs with 
|[expr] -> expr 
|_ -> Seq(exprs) in

match sexpr with
| Pair(Symbol("quasiquote"),Pair(sexp,Nil)) -> tag_parse (expendQuasy sexp)
| Pair(Symbol("and"),sexp) -> tag_parse (macro_expansion_and sexp)
| Pair(Symbol("let*"), _) -> tag_parse (macro_expansion_let_star sexpr)
| Pair(Symbol("let"), Pair(Nil, body)) -> tag_parse (macro_expansion_let sexpr)
| Pair(Symbol("let"), Pair(Pair(rib, ribs), body)) ->  tag_parse (macro_expansion_let sexpr)
| Pair(Symbol("letrec"),Pair(ribs, body)) -> tag_parse (macro_expansion_letrec sexpr)
| Pair(Symbol("cond"), ribs) -> tag_parse (macro_expansion_cond ribs)
| Pair(Symbol("begin"), Nil) -> Const(Void)
| Pair(Symbol("begin"), Pair(sexp, Nil)) -> tag_parse sexp 
| Pair(Symbol("begin"), list_of_exp) -> Seq(pair_to_list tag_parse list_of_exp)
| Pair(Symbol("or") , list_of_params) -> let exp_list = pair_to_list tag_parse list_of_params in 
 if (exp_list == []) then Const(Sexpr(Bool(false))) else if (List.length(exp_list) == 1) then List.hd(exp_list) else Or(exp_list)
| Pair(Symbol("set!"), Pair(id, Pair (value,Nil))) -> Set((tag_parse id),(tag_parse value))
| Pair(Symbol("define"), Pair(Symbol(nameVar) , Pair(exp , Nil))) -> Def(tag_parse (Symbol(nameVar)), tag_parse exp)
| Pair(Symbol("define"), Pair(Pair(Symbol(name), args), body)) -> tag_parse (macro_expansion_MIT_define sexpr)
| Pair(Symbol("lambda"), Pair(Symbol(sym), body))-> LambdaOpt([],sym, tag_parse_body body)
| Pair(Symbol("lambda"), Pair(list_of_param, body))-> 
  let check = check_if_legal_args list_of_param in if(check = false) then raise X_syntax_error else
  let optional = getOptinal list_of_param in 
  if(optional = "") then LambdaSimple(pull_string list_of_param , tag_parse_body body)
  else LambdaOpt(pull_string list_of_param, optional, tag_parse_body body)
| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
 If(tag_parse  test, tag_parse dit, tag_parse dif)
| Pair(Symbol("if"), Pair(test,Pair(dit, Nil))) -> If(tag_parse  test, tag_parse dit, Const(Void))
| Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x)) 
| Pair(closure, args_list)-> Applic((tag_parse closure), (pair_to_list tag_parse args_list))
| Symbol(x) ->  if(isReserved(x) = false) then Var(x)  else raise X_syntax_error
| TagRef(x) -> Const(Sexpr(TagRef(x)))
| TaggedSexpr (st, Pair (Symbol "quote", Pair (x, Nil))) -> Const(Sexpr(TaggedSexpr(st, x)))
| TaggedSexpr (st,x) -> Const(Sexpr(TaggedSexpr(st, x)))
| Number(x) -> Const(Sexpr(Number(x)))
| Bool(x) -> Const(Sexpr(Bool(x)))
| Char(x) -> Const(Sexpr(Char(x)))
| String(x) -> Const(Sexpr(String(x)))
|_-> raise X_syntax_error;;

let tag_parse_expression sexpr = tag_parse sexpr;;


let tag_parse_expressions sexpr = List.map tag_parse sexpr;;

end;; (* struct Tag_Parser *)

