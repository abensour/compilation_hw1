#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_is_empty;;
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;
  
(*module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end *)
module Reader = struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;





(* lishay work *)
let digit = range '0' '9';;
let digits = plus digit;;
let plMin = disj (char '+') (char '-');;
let abc = (range 'a' 'z') ;;

(*liad's work *)
let punctuation = const (fun ch-> ch= '!' || ch= '$' || ch= '^' || ch='*' || ch='-' || ch='_' || ch='='
|| ch='+' || ch='<' || ch='>' || ch='/' || ch ='?');;
let symbolChar = disj_list [range_ci 'a' 'z'; digit ; punctuation];;
let symbolP = pack (plus symbolChar) (fun e -> 
let lowercase = List.map lowercase_ascii e in
Symbol(list_to_string lowercase));;
(*end liad's work*)

(* lishay work *)
 (*radix notation parser *)
let rorR = disj (char 'r') (char 'R') ;;
let radixStart =  caten (caten (char '#') digits) rorR ;; (* ((('#', ['2'; '4']), 'r'), ['e'; 'f']) *)
let getNumF base counterP char = 
let (integer,mult) = counterP in 
let charFloat =if (char >= 'a' && char <= 'z') then float_of_int((int_of_char char) - 87) else float_of_int((int_of_char char) - 48)
in if (charFloat >= (float_of_int base)) then raise X_no_match else
((integer +. (charFloat *. mult)), (mult /. (float_of_int base)));;
let getNumI base char counterP= 
let (integer,mult) = counterP in 
let charFloat =if (char >= 'a' && char <= 'z') then float_of_int((int_of_char char) - 87) else float_of_int((int_of_char char) - 48)
in if (charFloat >= (float_of_int base)) then raise X_no_match else ((integer +. (charFloat *. mult)), (mult*. (float_of_int base)));;
let digOLetter = plus (disj digit abc) ;;


let radixPs l = let (((e,base),r),bNumber) = radixStart l in 
let number = List.map lowercase_ascii bNumber in  
let ibase = int_of_string (list_to_string base) in 
if ibase > 36 then raise X_no_match
else 
let (sign,num) = 
match maybe plMin number with
| (None,e) -> ('+',e)
| (Some(result),e) -> (result,e) in
let (intB,floatb) = digOLetter num in (*([1;2;a;z;D;1],[.;d;S]*) 
let (fnum,length) = List.fold_right (getNumI ibase) intB (0.,1.) in (*fnum is the number ao the integer part*)
match floatb with
| [] -> if sign == '+' then (Number(Int (int_of_float fnum)),floatb) else (Number(Int (-1 * (int_of_float fnum))),floatb)
| chf :: esf ->  (* esf is the continue without the dot *)
if (chf != '.') then if sign == '+' then (Number(Int (int_of_float fnum)),floatb) else (Number(Int (-1 * (int_of_float fnum))),floatb) 
else  let (numFloat,rest) = digOLetter esf
in let (fnumc,lengthc) = List.fold_left (getNumF ibase) (0., 1. /. (float_of_int ibase)) numFloat in (*fnum is the number ao the integer part*)
if sign == '+' then (Number(Float(fnum +. fnumc)),rest) else (Number(Float(-1. *. (fnum +. fnumc))),rest) 
let radixP = not_followed_by radixPs symbolChar;;
(* ['+';'3';'5';'f'] -> (['+'; '3'; '5'], ['f']) *)
let integerstart l= 
match maybe plMin l with
| (None,e) -> digits e
| (Some(result),e) ->
let (intg,rest) = digits e in
((result :: intg) ,rest);;


let integerPs l= 
let (number,sec) = integerstart l in (* get the number and the continuence *)
match sec with
| [] -> (Number(Int(int_of_string (list_to_string number))) ,[])  (*if no continuence than build the number*)
| ch :: es ->  (* there is some continuation can be symbol/float/exponent *)
if ((lowercase_ascii ch) == 'e') then
  let (exponent,rest) = integerstart es in  
  let fNumber = float_of_string (list_to_string number) in
  let fExpo = float_of_string (list_to_string exponent) in
  let fullNum = fNumber *. (10. ** fExpo) in 
  if (float_of_int(int_of_float fullNum) = fullNum) then (Number (Int (int_of_float fullNum)),rest)
  else (Number (Float  fullNum),rest)
else if ((lowercase_ascii ch) == '.') then raise X_no_match else (Number(Int(int_of_string (list_to_string number))) ,sec);;
let integerP = not_followed_by integerPs symbolChar;;

let floatPs l= 
let (number,sec) = integerstart l in (* get the number and the continuence *)
match sec with
| [] -> (Number(Int(int_of_string (list_to_string number))),[])
| chf :: esf ->  (* there is some continuation can be symbol/float *)
if (chf == '.') then
  let (decimal,drest) = digits esf in 
  let fNum =(float_of_string (list_to_string (number @ ['.'] @ decimal))) in
  match drest with
  |[] ->  (Number(Float(fNum)),drest)
  |ch :: es ->  (* there is some continuation can be symbol/float/exponent *)
  if ((lowercase_ascii ch) == 'e') then
    let (exponent,rest) = integerstart es in 
    let fExpo = float_of_string (list_to_string exponent) in
    let fullNum = fNum *. (10. ** fExpo) in 
    if (float_of_int(int_of_float fullNum) = fullNum) then (Number (Int (int_of_float fullNum)),rest)
    else (Number (Float  fullNum),rest)
  else (Number(Float(fNum)),drest)
else raise X_no_match ;;
let floatP = not_followed_by floatPs symbolChar;;
(*liad's work*)
let boolP = 
let tOrf = disj (word_ci "#t") (word_ci "#f") in 
pack tOrf (fun (boolean)-> 
match boolean with
| [_;'t'] -> Bool(true)
| [_;'T'] -> Bool(true)
| _ -> Bool(false));;

let nilP s = match s with
|[] -> Nil
|_ -> raise X_no_match;;

let make_range_char leq ch1 (s : char list) =
  pack (const (fun ch -> (leq ch1 ch))) (fun (e)-> [e]) s;;

let rangeChar = make_range_char (fun ch1 ch2 -> ch1 < ch2);;

let visibleSimpleChar = rangeChar  ' ';;

let newline = pack (word_ci "newline") (fun l -> ['1';'0']);; 
let nul = pack (word_ci "nul") (fun l -> ['0']);; 
let space = pack (word_ci "space") (fun l -> ['3'; '2']);;
let tab = pack (word_ci "tab") (fun l -> ['9']);;
let page = pack (word_ci "page") (fun l -> ['1';'2']);;
let return = pack (word_ci "return") (fun l -> ['1'; '3']);;

let namedChar s = 
try disj newline nul s 
with X_no_match -> try disj space tab s
with X_no_match -> try disj page return s 
with X_no_match -> raise X_no_match;;

let charP  =  
pack (caten (word "#\\") (disj namedChar visibleSimpleChar))
(fun (l, e) -> match e with
| ch::[] -> Char(ch)
| es -> Char(char_of_int(int_of_string(list_to_string es))));;

(* support in 34 is missing *)
(*ascii code of special char*)
let doubleQuoteInS = pack (word "\\\"") (fun e -> '\"');;
let otherMetaChar = const (fun ch -> ch= char_of_int(13) || ch= char_of_int(10) 
|| ch= char_of_int(9)|| ch= char_of_int(12)|| ch= char_of_int(92)) ;;
let stringMetaChar = disj doubleQuoteInS otherMetaChar;;
let stringLiteralChar = const (fun ch -> ch != '"' && ch != '\\' );;
let stringChar = disj stringLiteralChar stringMetaChar ;;
let doubleQuote = char '"';;

let stringP  =  
let pars = caten (caten doubleQuote (star stringChar)) doubleQuote in (* (((a,b),c),[])*)
pack pars (fun ((l,s),r) -> String(list_to_string(s))) ;;


let unested_sexpr_parser s = 
disj_list [integerP ;boolP; charP; stringP; symbolP] s ;; 

(*taken from practice lesson*)
let make_paired nt_left nt_right nt =
let nt = caten nt_left nt in
let nt = pack nt (function (_, e) -> e) in
let nt = caten nt nt_right in
let nt = pack nt (function (e, _) -> e) in
  nt;;

(*erase maybe*)
let nt_whitespaces = star (char ' ');;

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;
(*erase maybe*)


let tok_dot = make_spaced (char '.');;
(**)
(*seperate comments from the sexpr like make_spaces*)
(*line comments*)
let any_char_but_semi = const (fun ch -> ch != ';');; 
let semiP = pack (char ';') (fun e-> [e]);; 
let any_char_but_newline = const (fun ch -> ch != '\n');; 
let end_of_line_or_input = disj (nt_end_of_input) (pack (char '\n') (fun e-> [e]));;
let line_commentsP  = pack (caten (caten semiP (star any_char_but_newline)) end_of_line_or_input)
(fun ((semi, chars),end_of)-> [' ']) ;; 

let whitespace = (pack (char ' ') (fun e-> [e]));;
let whitespaces_or_comment = disj line_commentsP whitespace;;
let make_line_comments_or_whitespaces nt = make_paired (star whitespaces_or_comment) (star whitespaces_or_comment) nt;;

let tok_lparen =  make_line_comments_or_whitespaces (char '(');;

let tok_rparen = make_line_comments_or_whitespaces( char ')');;

type mList = { mutable listtags : string list };;
let tagsList = { listtags = []};;

let tagP = pack (caten (caten (word "#{") symbolP) (word "}")) (fun ((a,sexp),b) -> 
match sexp with
|Symbol(str) -> let () = tagsList.listtags <- str ::tagsList.listtags in TagRef(str)
|_ -> raise X_no_match);;

let updateL str =
let (updated, counter) = List.fold_right (fun curr_str (list_acc, count_acc) -> 
if  (curr_str = str) then if (count_acc >= 1) (*already erase one*)
then (curr_str ::list_acc, count_acc +1 ) else (list_acc, count_acc +1)
else (curr_str :: list_acc, count_acc)) tagsList.listtags ([], 0)
in  let () = tagsList.listtags <- updated in counter;;

(*returns (sexp, rest of list) *)
let rec nested_sexpr_parser l =
let qoutedP = pack (caten (word "'") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol "quote", Pair(s, Nil))) in

let quasiP = pack (caten (word "`") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol "quasiqoute", Pair(s, Nil))) in

let unqouteSpliceP = pack (caten (word ",@") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol "unquote-splicing", Pair(s, Nil))) in

let unqoutP = pack (caten (word ",") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol "unquote", Pair(s, Nil))) in

let quate_parser = disj_list [qoutedP ; quasiP ; unqouteSpliceP; unqoutP] in

(* ( (  ('(', [sexp1;sexp2;...])  , ')' ), rest list ) *)
(*make it a nested pair *)
(* check empty list*)
let listP =   pack (caten (caten tok_lparen (star nested_sexpr_parser)) tok_rparen)
(fun ((lpar, list_of_sexp), rpar) -> List.fold_right (fun curr acc ->  Pair(curr, acc)) list_of_sexp Nil) in

let dottedListP = 
pack (caten (caten (caten (caten tok_lparen (plus nested_sexpr_parser)) tok_dot) nested_sexpr_parser )tok_rparen)
(fun ((((lpar, list_of_sexp), dot), sp), rpar) -> List.fold_right 
(fun curr acc ->  Pair(curr, acc)) list_of_sexp sp) in

let exprTag =  caten (word "=") nested_sexpr_parser in

let  taggedSexprP = pack (caten tagP (maybe exprTag)) (fun (tag, maybeR) ->
match tag, maybeR with 
| TagRef(tag_str), None -> let dTimes = updateL tag_str  in  if (dTimes > 1) then tag (*means is still the tag in the list *)
  else raise X_this_should_not_happen
| TagRef(tag_str),Some((a, sexp)) -> let dTimes = updateL tag_str in if (dTimes > 1) then raise X_this_should_not_happen (*the name alrady existed*)
  else let () = tagsList.listtags <- tag_str :: tagsList.listtags in TaggedSexpr(tag_str, sexp)
| _, _ -> raise X_no_match) in

let sexpr_commentP l =  let (((com1, com2) , sexpr_com), rest) =  caten (caten (word "#;") nt_whitespaces) nested_sexpr_parser l
in nested_sexpr_parser rest in
let list_of_parsers = [unested_sexpr_parser; quate_parser; listP; dottedListP; sexpr_commentP ;taggedSexprP] in

disj_list list_of_parsers l;;

(*main method gets string returns sexp*)
let read_sexpr string = 
let list_of_char = string_to_list string in 
let (sexpr, rest) = nested_sexpr_parser list_of_char
in sexpr;;

let read_sexprs string = 
let list_of_char = string_to_list string in 
let (sexpr_list, rest) = (star nested_sexpr_parser)  list_of_char
in sexpr_list;; 

 
end;; (* struct Reader *)
