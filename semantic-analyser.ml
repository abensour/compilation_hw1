#use "reader.ml";;
open Reader;;

#use "tag-parser.ml";;
open Tag_Parser;;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct
type pairs = {car : string ;  cdr : int};;
type bPairs = {name: string ;  depth : int ; indx : int};;
type pList = { params:  pairs list };;
type bList = { bounds :  bPairs list };;
let rec lexicalP (pl:pairs list) (bl:bPairs list) e =
match e with
  | Const(const) ->Const'(const)
  | Var(str) -> let pval = List.find_all (fun (param:pairs) -> param.car = str) pl
  in if(pval != []) then Var'(VarParam((List.hd pval).car,(List.hd pval).cdr))
  else let bval = List.fold_left (fun (acc:bPairs) (cur:bPairs) -> if ((cur.name = str) && ((cur.depth < acc.depth) || (acc.depth == -1))) then cur else acc) {name = ""; depth = -1; indx = -1} bl 
  in if (bval.depth != -1) then Var'(VarBound(bval.name,bval.depth,bval.indx)) else Var'(VarFree(str))
  | If(test,th,els) -> If'(lexicalP pl bl test ,lexicalP pl bl th,lexicalP pl bl els)
  | Seq(expL) -> let exp'L = List.map (fun exp1 -> lexicalP pl bl exp1) expL in Seq'(exp'L)
  | Set (name,value) -> Set'(lexicalP pl bl name,lexicalP pl bl value)
  | Def (name,value) -> Def'(lexicalP pl bl name,lexicalP pl bl value)
  | Or(expL) -> let exp'L = List.map (fun exp1 -> lexicalP pl bl exp1) expL in Or'(exp'L)
  | LambdaSimple(strL,body) -> 
   let bl1 = List.map (fun (arg:bPairs) ->  {name = arg.name ; depth = (arg.depth + 1) ; indx = arg.indx }) bl (*update depth*)
   in let ptob = List.map (fun (par:pairs) -> {name = par.car ; depth = 0; indx = par.cdr}) pl (*convert ols params to bounds*) 
   in let bl2 = bl1 @ ptob (*add old params to bounds list*) in 
   let (pl1,length) = List.fold_left (fun (nparams,ind) str -> ({car = str ; cdr = ind} :: nparams ,(ind + 1))) ([],0) strL (*add new params*)
   in LambdaSimple'(strL , (lexicalP pl1 bl2 body)) 
  | LambdaOpt(strL,optStr,body) ->
     let bl1 = List.map (fun (arg:bPairs) ->  {name = arg.name ; depth = (arg.depth + 1) ; indx = arg.indx }) bl (*update depth*)
   in let ptob = List.map (fun (par:pairs) -> {name = par.car ; depth = 0; indx = par.cdr}) pl (*convert ols params to bounds*) 
   in let bl2 = bl1 @ ptob (*add old params to bounds list*) in 
    let (pl1,length) = List.fold_left (fun (nparams,ind) str -> ({car = str ; cdr = ind} :: nparams ,(ind + 1))) ([],0) strL (*add new params*)
   in let pl2 =  {car = optStr ; cdr = length} :: pl1 in LambdaOpt'(strL , optStr, (lexicalP pl2 bl2 body)) 
  | Applic(proc,args) -> let args' = List.map (fun currExp -> (lexicalP pl bl currExp)) args in let proc' = (lexicalP pl bl proc) in Applic'(proc',args') ;;

let annotate_lexical_addresses e = lexicalP [] [] e;;

let annotate_tail_calls e = raise X_not_yet_implemented;;

let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
