#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
(*module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))] 
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;*)
(*module Code_Gen : CODE_GEN = struct*)
module Code_Gen = struct
  let rec make_list_of_all_consts ast = match ast with 
  | Const'(const) -> [const]
  | BoxSet'(var_name, expr) -> make_list_of_all_consts expr
  | If'(test, dit, dif) -> (make_list_of_all_consts test) @ (make_list_of_all_consts dit) @ (make_list_of_all_consts dif)
  | Seq'(expr_list) -> List.flatten(List.map make_list_of_all_consts expr_list) 
  | Set'(var, expr)-> make_list_of_all_consts expr
  | Def'(var, expr) -> make_list_of_all_consts expr
  | Or'(expr_list) -> List.flatten(List.map make_list_of_all_consts expr_list) 
  | LambdaSimple'(args, expr)-> make_list_of_all_consts expr 
  | LambdaOpt'(args, optional, expr) -> make_list_of_all_consts expr
  | Applic'(closure, params)-> (make_list_of_all_consts closure) @  List.flatten(List.map make_list_of_all_consts params)
  | ApplicTP'(closure, params)-> (make_list_of_all_consts closure) @  List.flatten(List.map make_list_of_all_consts params)
  | _ -> [];;

  let rec extend_consts_table const = match const with
    | Sexpr(Symbol(string)) -> [Sexpr(String(string)); const]
    | Sexpr(Pair(car_const, cdr_const)) -> (extend_consts_table (Sexpr(car_const))) @  (extend_consts_table (Sexpr(cdr_const))) @ [const]
    | Sexpr(TaggedSexpr(string, sexpr)) -> extend_consts_table (Sexpr(sexpr))
    |_-> [const];;

  let exists curr_const consts_list = 
    List.fold_right (fun curr acc -> 
    match curr, curr_const with
    |Sexpr(sexp1), Sexpr(sexp2) -> if (sexpr_eq sexp1 sexp2) then true else acc
    |Void , Void ->  true
    |_,_-> acc) consts_list false;;
  
  let reduce_list l = 
    List.fold_right (fun curr acc -> if(exists curr acc) then acc else curr::acc) l [];;

  let get_const_address table const = 
  List.fold_left (fun acc (curr_const, (offset, string))-> match curr_const, const with 
  |Void , Void ->  offset 
  |Sexpr(sexp1), Sexpr(sexp2) -> if (sexpr_eq sexp1 sexp2) then offset else acc
  |_,_-> acc) (-1) table;; (*maybe throw an error???*)
  
   let get_const_address_2 table const = 
  List.fold_left (fun acc (curr_const, (offset, string))-> match curr_const, const with 
  |Void , Void ->  offset 
  |Sexp(TagRef(name1)), Sexp(TagRef(name2)) -> if(name1 = name2) then (get_const_address map.get(name1))
  |Sexpr(sexp1), Sexpr(sexp2) -> if (sexpr_eq sexp1 sexp2) then offset else acc
  |_,_-> acc) (-1) table;; (*maybe throw an error???*)

  (*returns entry and the size of the const*)
  let build_const_entry const table offset = match const with 
  |Void -> ( (const, (offset, "MAKE_VOID")) , 1)
  |Sexpr(Nil) -> ( (const, (offset, "MAKE_NIL")), 1)
  |Sexpr(Bool false) -> ( (const, (offset, "MAKE_BOOL(0)")), 2)
  |Sexpr(Bool true) -> ( (const, (offset, "MAKE_BOOL(1)")), 2)
  |Sexpr(Number(Int(num))) -> ( (const, (offset, "MAKE_LITERAL_INT(" ^ (string_of_int num) ^")")), 9)
  |Sexpr(Number(Float(num))) -> ( (const, (offset, "MAKE_LITERAL_FLOAT(" ^ (string_of_float num) ^")")), 9)
  |Sexpr(Char(c)) -> ( (const, (offset, "MAKE_LITERAL_CHAR("^ (Char.escaped c) ^")")), 2)
  |Sexpr(String(str)) -> ( (const, (offset, " MAKE_LITERAL_STRING(\" "^ str ^" \")")), (String.length str) + 9) (*to check!*)
  |Sexpr(Symbol(str)) -> ( (const, (offset, " MAKE_LITERAL_SYMBOL(consts+ "^ (string_of_int (get_const_address table (Sexpr(String(str))))) ^")")), 9)
  |Sexpr(Pair(sexpr1, sexpr2)) -> ( (const, (offset, " MAKE_LITERAL_PAIR(consts+ "^ (string_of_int (get_const_address table (Sexpr(sexpr1)))) ^"
  , consts+" ^ (string_of_int (get_const_address table (Sexpr(sexpr2)))) ^")")), 17)
  |Sexpr(TagRef(name)) -> let exp = map.get(name) build_const_entry(exp)
  

  let build_consts_table consts_list = 
  let (table, last_offset) = 
  List.fold_left (fun (table, offset) curr -> 
  let (const_entry, size_of_const) = build_const_entry curr table offset in
  (table@[const_entry], offset+size_of_const ))  ([], 0) consts_list
  in table;;
  

  let check string = 
  let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s)) 
  in
  let asts = string_to_asts string in 
  let must_const = [Void ;Sexpr(Nil); Sexpr(Bool false) ; Sexpr(Bool true)] in
  let list_of_consts = List.flatten (List.map make_list_of_all_consts asts) in
  let extended_list = must_const @ List.flatten(List.map extend_consts_table list_of_consts) in
  let () = biuld_table expand_list in
  let reduced = reduce_list extended_list in
  let table_1 = build_consts_table reduced in build_consts_table reduced table

  let make_consts_tbl asts = 
  let must_const = [Void ;Sexpr(Nil); Sexpr(Bool false) ; Sexpr(Bool true)] in
  let list_of_consts = List.flatten (List.map make_list_of_all_consts asts) in
  let extended_list = must_const @ List.flatten (List.map extend_consts_table list_of_consts) in
  let reduced = reduce_list extended_list in
  build_consts_table reduced;;

let exists_str curr_const consts_list = 
  List.fold_left (fun acc curr -> if (curr = curr_const) then true else acc) false consts_list;;
  
let reduce_list_str l = 
  List.fold_right (fun curr acc -> if(exists_str curr acc) then acc else [curr]@acc) l [];;


let primitive_names = 
  ["boolean?"; "float?"; "integer?"; "pair?"; "null?"; "char?"; "string?"; "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string"; "symbol->string"; "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "=" (* you can add yours here *)];;


let rec fvars_list_from_exp exp'  = 
match exp' with 
  | Var'(VarFree(var_name)) ->  [var_name] 
  | If'(test, dit, dif) -> (fvars_list_from_exp test) @ (fvars_list_from_exp dit) @ (fvars_list_from_exp dif) 
  | Seq'(expr_list) -> List.fold_left (fun acc_list expr -> acc_list @ fvars_list_from_exp expr) [] expr_list
  | Set'(Var'(VarFree(var_name)), expr) -> [var_name] @ fvars_list_from_exp expr
  | Set'(Var'(_), expr) -> fvars_list_from_exp expr
  | Def'(var, expr) -> fvars_list_from_exp var @ fvars_list_from_exp expr
  | Or'(expr_list ) -> List.fold_left (fun acc_list expr -> acc_list @ fvars_list_from_exp expr) [] expr_list
  | LambdaSimple'(_, bodyL) -> fvars_list_from_exp bodyL
  | LambdaOpt'(_,_, bodyL)-> fvars_list_from_exp bodyL
  | Applic'(closure, args) -> fvars_list_from_exp closure @ List.fold_left (fun acc_list expr -> acc_list @ fvars_list_from_exp expr) [] args
  | ApplicTP'(closure, args) -> fvars_list_from_exp closure @ List.fold_left (fun acc_list expr -> acc_list @ fvars_list_from_exp expr) [] args
  | BoxSet'(var, expr) -> fvars_list_from_exp expr
  |_-> [];;
(*[("boolean?" , 0);("is_boolean", 1)]*)
let gen_fvars_table asts = let fvars_list = List.fold_left (fun acclist exp' -> acclist@ (fvars_list_from_exp exp')) [] asts in
let fvars_set = reduce_list_str (primitive_names@fvars_list) in 
let (fvars_table,_) = List.fold_left (fun (acclist,indx) str -> ((acclist @ [(str,indx)]),( indx + 1))) ([],0) fvars_set in fvars_table;;



  let make_fvars_tbl asts = gen_fvars_table asts;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

