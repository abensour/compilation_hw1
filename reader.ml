
#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
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
let car = (function (e, _) -> e);;
let cdr = (function (_,e) -> e);;
let digit = range '0' '9';;
let digits = plus digit;;
let plMin = disj (char '+') (char '-');;

(* ['+';'3';'5';'f'] -> (['+'; '3'; '5'], ['f']) *)
let integerstart l= 
match maybe plMin l with
| (None,e) -> digits e
| (Some(result),e) ->
let (intg,rest) = digits e in
((result :: intg) ,rest);;

let integerP l= 
let (number,sec) = integerstart l in (* get the number and the continuence *)
match sec with
| [] -> Number(Int(int_of_string (list_to_string number)))  (*if no continuence than build the number*)
| ch :: es ->  (* there is some continuation can be symbol/float/exponent *)
if ((lowercase_ascii ch) == 'e') then
  let (exponent,rest) = integerstart es in 
  if (rest != []) then raise X_this_should_not_happen
  else 
  let iNumber = int_of_string (list_to_string number) in
  let iExpo = int_of_string (list_to_string exponent) in
  let fullNum = iNumber * (pow 10 iExpo) in 
  Number(Int fullNum) 
else raise X_no_match ;;

let floatP l= 
let (number,sec) = integerstart l in (* get the number and the continuence *)
match sec with
| [] -> raise X_no_match
| chf :: esf ->  (* there is some continuation can be symbol/float *)
if (chf == '.') then
  let (decimal,drest) = digits esf in 
  let fullNum =(float_of_string (list_to_string (number @ ['.'] @ decimal))) in
  match drest with
  |[] ->  Number(Float(fullNum))
  |ch :: es ->  (* there is some continuation can be symbol/float/exponent *)
  if ((lowercase_ascii ch) == 'e') then
    let (exponent,rest) = integerstart es in 
    if (rest != []) then raise X_no_match
    else 
    let iExpo = int_of_string (list_to_string exponent) in
    let fullNumExp = fullNum *. (float_of_int (pow 10 iExpo)) in 
    Number(Float fullNum) 
  else raise X_no_match 
else raise X_no_match ;;

(* let charI = lowercase_ascii
match (let nextchar = lowercase_ascii((function (e :: es) -> e) sec)) with
| e -> (*exponent*) 
| . -> (*float*)
| _ -> (*check symbol / no match*) *)


 (* let nt_whitespaces = star (char ' ');;
let make_paired nt_left nt_right nt =
let nt = caten nt_left nt in
let nt = pack nt (function (_, e) -> e) in
let nt = caten nt nt_right in
let nt = pack nt (function (e, _) -> e) in
  nt;;
let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;
let tok_digits = make_spaced digits ;; *)

(*check capital letter*) 
(*liad's work*)
let boolP = 
let tOrf = disj (word "#t") (word "#f") in 
pack tOrf (fun (boolean)-> 
match boolean with
| [_;'t'] -> Bool(true)
| _ -> Bool(false));;

let make_range_char leq ch1 (s : char list) =
  pack (const (fun ch -> (leq ch1 ch))) (fun (e)-> [e]) s;;

let rangeChar = make_range_char (fun ch1 ch2 -> ch1 < ch2);;

let visibleSimpleChar = rangeChar  ' ';;

let newline = pack (word "newline") (fun l -> ['1';'0']);; 
let nul = pack (word "nul") (fun l -> ['0']);; 
let space = pack (word "space") (fun l -> ['3'; '2']);;
let tab = pack (word "tab") (fun l -> ['9']);;
let page = pack (word "page") (fun l -> ['1';'2']);;
let return = pack (word "return") (fun l -> ['1'; '3']);;

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
let stringMetaChar = const (fun ch -> ch= char_of_int(13) || ch= char_of_int(10)
|| ch= char_of_int(9)|| ch= char_of_int(12)|| ch= char_of_int(92)) ;;
let stringLiteralChar = const (fun ch -> ch != '"' && ch != '\\' );;
let stringChar = disj stringLiteralChar stringMetaChar ;;
let doubleQuote = char '"';;

let stringP  =  
let pars = caten (caten doubleQuote (star stringChar)) doubleQuote in (* (((a,b),c),[])*)
pack pars (fun ((l,s),r) -> String(list_to_string(s))) ;;

let unested_sexpr_parser s = 
disj_list [boolP; charP; stringP] s ;; 

(*quated*)


let qoute_to_string q =
 match q with
|['\''] -> "quote"
|['`'] -> "quasiqoute"
|[',';'@'] -> "unquote-splicing"
|[',']-> "unquote"
|_ -> "";;


(*taken from practice lesson*)
let make_paired nt_left nt_right nt =
let nt = caten nt_left nt in
let nt = pack nt (function (_, e) -> e) in
let nt = caten nt nt_right in
let nt = pack nt (function (e, _) -> e) in
  nt;;


let nt_whitespaces = star (char ' ');;

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let tok_lparen = make_spaced ( char '(');;

let tok_rparen = make_spaced ( char ')');;

let tok_dot = make_spaced (char '.');;
(**)
(*returns (sexp, rest of list) *)
let rec nested_sexpr_parser l=
let qoutedP = pack (caten (word "'") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol(qoute_to_string q ), Pair(s, Nil))) in

let quasiP = pack (caten (word "`") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol(qoute_to_string q), Pair(s, Nil))) in

let unqouteSpliceP = pack (caten (word ",@") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol(qoute_to_string q), Pair(s, Nil))) in

let unqoutP = pack (caten (word ",") nested_sexpr_parser) 
(fun (q, s) -> Pair(Symbol(qoute_to_string q), Pair(s, Nil))) in

let quate_parser = disj_list [qoutedP ; quasiP ; unqouteSpliceP; unqoutP] in

(* ( (  ('(', [sexp1;sexp2;...])  , ')' ), rest list ) *)
(*make it a nested pair *)
(* check empty list*)
let listP =   pack (caten (caten tok_lparen (star nested_sexpr_parser)) tok_rparen)
(fun ((lpar, list_of_sexp), rpar) -> List.fold_right (fun curr acc -> Pair(curr, acc)) list_of_sexp Nil)
in

let dottedListP = 
pack (caten (caten (caten (caten tok_lparen (plus nested_sexpr_parser)) tok_dot )nested_sexpr_parser )tok_rparen)
(fun ((((lpar, list_of_sexp), dot), sp), rpar) -> List.fold_right (fun curr acc -> Pair(curr, acc)) list_of_sexp sp)
in

let list_of_parsers = [unested_sexpr_parser; quate_parser; listP; dottedListP] in
disj_list list_of_parsers l ;;


(*main method gets string returns sexp*)
let read_sexpr string = 
let list = string_to_list string in 
nested_sexpr_parser list;;
  
let read_sexprs string = raise X_not_yet_implemented;;


  
end;; (* struct Reader *)
