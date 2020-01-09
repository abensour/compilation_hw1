#use "semantic-analyser.ml";;
exception X_this_should_not_happen;;
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
  type pairsList = { mutable pairsL :  (string*sexpr) list };;
  let pList = { pairsL = []};;

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
    List.fold_left (fun acc curr -> 
    match curr, curr_const with
    |Sexpr(sexp1), Sexpr(sexp2) -> if (sexpr_eq sexp1 sexp2) then true else acc
    |Void , Void ->  true
    |_,_-> acc) false consts_list;;
  
  let reduce_list l = 
    List.fold_left (fun  acc curr -> if(exists curr acc) then acc else acc@[curr]) [] l;;

  let get_const_address table const = 
  List.fold_left (fun acc (curr_const, (offset, string))-> match curr_const, const with 
  |Void , Void ->  offset 
  |Sexpr(sexp1), Sexpr(sexp2) -> if (sexpr_eq sexp1 sexp2) then offset else acc
  |_,_-> acc) (-1) table;; (*maybe throw an error???*)
  
  let rec get_const_address_iter_2 table const = 
  List.fold_left (fun acc (curr_const, (offset, string))-> match curr_const, const with 
  |Void , Void ->  offset 
  |Sexpr(TagRef(name1)), Sexpr(TagRef(name2)) -> if(name1 = name2) then let sexp = List.assoc name1 pList.pairsL in get_const_address_iter_2 table (Sexpr(sexp)) else acc
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
  |Sexpr(Symbol(str)) -> ( (const, (offset, " MAKE_LITERAL_SYMBOL(const_tbl+ "^ (string_of_int (get_const_address table (Sexpr(String(str))))) ^")")), 9)
  |Sexpr(Pair(sexpr1, sexpr2)) -> ( (const, (offset, " MAKE_LITERAL_PAIR(const_tbl+ "^ (string_of_int (get_const_address table (Sexpr(sexpr1)))) ^"
  , const_tbl+" ^ (string_of_int (get_const_address table (Sexpr(sexpr2)))) ^")")), 17)
  |Sexpr(TagRef(name)) -> ((const, (offset, "")) , 0)
  |_-> raise X_this_should_not_happen;;
  
  let build_const_entry_iter_2 (const,(offset,string)) table offset = match const with
  |Void -> ( (const, (offset, "MAKE_VOID")) , 1)
  |Sexpr(Nil) -> ( (const, (offset, "MAKE_NIL")), 1)
  |Sexpr(Bool false) -> ( (const, (offset, "MAKE_BOOL(0)")), 2)
  |Sexpr(Bool true) -> ( (const, (offset, "MAKE_BOOL(1)")), 2)
  |Sexpr(Number(Int(num))) -> ( (const, (offset, "MAKE_LITERAL_INT(" ^ (string_of_int num) ^")")), 9)
  |Sexpr(Number(Float(num))) -> ( (const, (offset, "MAKE_LITERAL_FLOAT(" ^ (string_of_float num) ^")")), 9)
  |Sexpr(Char(c)) -> ( (const, (offset, "MAKE_LITERAL_CHAR("^ (Char.escaped c) ^")")), 2)
  |Sexpr(String(str)) -> ( (const, (offset, " MAKE_LITERAL_STRING(\" "^ str ^" \")")), (String.length str) + 9) (*to check!*)
  |Sexpr(Symbol(str)) -> ( (const, (offset, " MAKE_LITERAL_SYMBOL(const_tbl+ "^ (string_of_int (get_const_address_iter_2 table (Sexpr(String(str))))) ^")")), 9)
  |Sexpr(Pair(sexpr1, sexpr2)) ->  ( (const, (offset, " MAKE_LITERAL_PAIR(const_tbl+ "^ (string_of_int (get_const_address_iter_2 table (Sexpr(sexpr1)))) ^"
  , const_tbl+" ^ (string_of_int (get_const_address_iter_2 table (Sexpr(sexpr2)))) ^")")), 17)
  |Sexpr(TagRef(name)) -> ((const, (offset, "")) , 0)
  |_ -> raise X_this_should_not_happen;;
  

  let build_consts_table_iter_2 table_1 = 
  let (table, last_offset) = 
  List.fold_left (fun (table, offset) curr -> 
  let (const_entry, size_of_const) = build_const_entry_iter_2 curr table_1 offset in
  match const_entry with 
  |(Sexpr(TagRef(_)),(_,_)) -> (table, offset)
  |_ -> (table @[const_entry], offset+size_of_const ))  ([], 0) table_1
  in table;;
  
  let build_consts_table consts_list = 
  let (table, last_offset) = 
  List.fold_left (fun (table, offset) curr -> 
  let (const_entry, size_of_const) = build_const_entry curr table offset in
  (table@[const_entry], offset+size_of_const ))  ([], 0) consts_list
  in table;;
  
  let rec rename_const const indx =
 match const with 
  | Pair(car_const, cdr_const) -> Pair((rename_const car_const indx), (rename_const cdr_const indx))
  | TaggedSexpr(string, sexpr) -> let renamed_string = string ^ "_" ^ string_of_int indx in TaggedSexpr(renamed_string,rename_const sexpr indx )
  | TagRef(string) -> let renamed_string = string ^ "_" ^ string_of_int indx in TagRef(renamed_string)
  |_-> const;;


let rec rename_reffs exp' indx = match exp' with
  | Const'(Sexpr(expr)) -> Const'(Sexpr(rename_const expr indx))
  | BoxSet'(var_name, expr) -> BoxSet'(var_name, rename_reffs expr indx)
  | If'(test, dit, dif) -> If'((rename_reffs test indx) , (rename_reffs dit indx) , (rename_reffs dif indx))
  | Seq'(expr_list) -> Seq'(List.map (fun exp -> rename_reffs exp indx) expr_list) 
  | Set'(var, expr)-> Set'(var, rename_reffs expr indx)
  | Def'(var, expr) -> Def'(var , rename_reffs expr indx)
  | Or'(expr_list) -> Or'(List.map (fun exp -> rename_reffs exp indx) expr_list) 
  | LambdaSimple'(args, expr)->  LambdaSimple'(args,rename_reffs expr indx) 
  | LambdaOpt'(args, optional, expr) -> LambdaOpt'(args, optional, rename_reffs expr indx)
  | Applic'(closure, params)-> Applic'(rename_reffs closure indx, (List.map (fun exp -> rename_reffs exp indx) params)) 
  | ApplicTP'(closure, params)-> Applic'(rename_reffs closure indx, (List.map (fun exp -> rename_reffs exp indx) params)) 
  | _ -> exp';;

let rec remove_tagged const  =
 match const with 
  | Pair(car_const, cdr_const) -> Pair((remove_tagged car_const ), (remove_tagged cdr_const ))
  | TaggedSexpr(string, sexpr) -> let expr = remove_tagged sexpr in let () = pList.pairsL <- (string,expr) :: pList.pairsL in expr
  |_-> const;;

let rec build_dictionary_and_remove_tagges exp' =
match exp' with  
  | Const'(Sexpr(expr)) -> Const'(Sexpr(remove_tagged expr))
  | BoxSet'(var_name, expr) -> BoxSet'(var_name, build_dictionary_and_remove_tagges expr)
  | If'(test, dit, dif) -> If'((build_dictionary_and_remove_tagges test ) , (build_dictionary_and_remove_tagges dit ) , (build_dictionary_and_remove_tagges dif ))
  | Seq'(expr_list) -> Seq'(List.map (fun exp -> build_dictionary_and_remove_tagges exp ) expr_list) 
  | Set'(var, expr)-> Set'(var, build_dictionary_and_remove_tagges expr )
  | Def'(var, expr) -> Def'(var , build_dictionary_and_remove_tagges expr )
  | Or'(expr_list) -> Or'(List.map (fun exp -> build_dictionary_and_remove_tagges exp ) expr_list) 
  | LambdaSimple'(args, expr)->  LambdaSimple'(args,build_dictionary_and_remove_tagges expr ) 
  | LambdaOpt'(args, optional, expr) -> LambdaOpt'(args, optional, build_dictionary_and_remove_tagges expr )
  | Applic'(closure, params)-> Applic'(build_dictionary_and_remove_tagges closure , (List.map (fun exp -> build_dictionary_and_remove_tagges exp ) params)) 
  | ApplicTP'(closure, params)-> Applic'(build_dictionary_and_remove_tagges closure , (List.map (fun exp -> build_dictionary_and_remove_tagges exp ) params)) 
  | _ -> exp';;

let rename_ast asts =
  let (asts_renamed,_) =  List.fold_left (fun (accList,indx) exp' -> (accList @ [(rename_reffs exp' indx)] , indx +1 )) ([],0) asts in 
  asts_renamed;;

  let make_consts_tbl asts = 
  let ast_without_tagggedSexpr =List.fold_left (fun accList curr -> accList @ [build_dictionary_and_remove_tagges curr]) [] asts in 
  let must_const = [Void ;Sexpr(Nil); Sexpr(Bool false) ; Sexpr(Bool true)] in
  let list_of_consts = List.flatten (List.map make_list_of_all_consts ast_without_tagggedSexpr) in
  let extended_list = must_const @ List.flatten (List.map extend_consts_table list_of_consts) in
  let reduced = reduce_list extended_list in
  let table_1 = build_consts_table reduced in build_consts_table_iter_2 table_1;; 

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


  let get_address_in_const_table constant consts_table = 
    "const_tbl+" ^ (string_of_int (get_const_address consts_table constant));;



  type mutable_int = {mutable index:int};; 
  let label_index = {index = 0};;

  let generate_lambda_simple generated_body str_index= 
 "mov rbx, [rbp + 8*2] ;;rbx = address of env
mov rcx, 0 ;;counter for size of env
count_env_length" ^ str_index ^":
    cmp qword rbx, SOB_NIL_ADDRESS
    je end_count_env_length" ^ str_index ^"
    add rbx, 8
    add rcx, 1 
    jmp count_env_length" ^ str_index ^"
end_count_env_length" ^ str_index ^": 
    push rcx
    add rcx,1 ;;size of extent env 
    shl rcx, 3 ;;mul rcx*8
    MALLOC rax, rcx 
    pop rcx ;;env size 
    mov rbx, [rbp + 8*2] 
;;rbx is oldenv adrees and rax is extenvadrees
    mov rsi, 0 ;;i
    mov rdi, 1 ;;j
copy_old_env" ^ str_index ^":
    cmp rsi, rcx
    je end_copy_old_env" ^ str_index ^" 
    mov rdx, [rbx + 8*rsi] ;;Env[i]
    mov [rax + 8*rdi], rdx ;;ExtEnv[j] = Env[i]
    inc rsi
    inc rdi 
    jmp copy_old_env" ^ str_index ^"

end_copy_old_env" ^ str_index ^":
    mov rdx, [rbp + 8*3]
    push rax
    push rdx 
    shl rdx, 3 ;;mul rdx*8
    MALLOC rbx, rdx ;;rbx is address of ExtEnv[0]
    pop rdx ;;number of params 
    pop rax ;;address of ExtEnv
    mov [rax], rbx  ;;put ExtEnv[0] address in ExtEnv Vector 
;;rbx is the pointer to the extenv[0] and rdx number of params 
    mov rcx,0
compy_params" ^ str_index ^":
    cmp rcx, rdx 
    je end_copy_params" ^ str_index ^" 
    mov rsi, rcx 
    shl rsi, 3 ;;for param number rcx  = mul rsi*8
    add rsi, 4*8 ;;for the zeroth param
    add rsi, rbp 
    ;;[rbp + 4*8 + rcx*8]
    mov rsi, [rsi]
    mov [rbx+rcx*8], rsi 
    inc rcx 
    jmp compy_params" ^ str_index ^"
end_copy_params" ^ str_index ^":
    mov rbx, rax 
    MAKE_CLOSURE(rax, rbx ,Lcode" ^ str_index ^") 
    jmp Lcont" ^ str_index ^" 
Lcode" ^ str_index ^":
    push rbp
    mov rbp, rsp \n"^ generated_body ^
 "\nleave
    ret 
Lcont" ^ str_index ^":";;

  let rec generate consts fvars e = match e with
  | Const'(constant)->  "mov rax, " ^ (get_address_in_const_table constant consts)
  | Var'(VarParam(_,minor)) -> "mov rax, qword [rbp + 8 * (4 + " ^ string_of_int minor ^ ")]"
  | Var'(VarBound(_,major,minor)) -> "mov rax, qword [rbp + 8 ∗ 2] \n mov rax, qword [rax + 8 ∗ " ^ string_of_int major ^"] \n mov rax, qword [rax + 8 ∗" ^ string_of_int minor ^ "]"  
  | Var'(VarFree(name)) -> "mov rax, qword [fvar_tbl+" ^  (string_of_int (List.assoc name fvars)) ^ "]"
  | BoxGet'(v)-> (generate consts fvars (Var'(v))) ^ "\n" ^ "mov rax, qword [rax]"
  | BoxSet'(v, exp)-> (generate consts fvars exp) ^ "\npush rax" ^ (generate consts fvars (Var'(v))) ^ "\npop qword [rax] \nmov rax, sob_void"
  | If'(test, dit, dif) -> let str =  (generate consts fvars test) ^ "\n" ^ "cmp rax, SOB_FALSE_ADDRESS" ^ "\n" ^ "je Lelse" ^ (string_of_int label_index.index)^  "\n"
  ^ (generate consts fvars dit) ^"\n" ^ "jmp Lexit" ^ (string_of_int label_index.index) ^ "\n" ^ "Lelse" ^ (string_of_int label_index.index) ^":\n" ^ (generate consts fvars dif) 
  ^ "\nLexit" ^(string_of_int label_index.index) ^ ":" in let () = label_index.index <- label_index.index + 1 in str 
  | Seq'(expr_list)-> List.fold_left (fun acc curr ->  acc ^ "\n" ^ (generate consts fvars curr)) "" expr_list 
  | Set'(Var'(VarParam(_, minor)), exp)-> (generate consts fvars exp) ^ "\n"^
  "mov qword [rbp + 8*(4+ " ^ (string_of_int minor) ^ ")], rax" ^"\n"^ 
  "mov rax, sob_void"
  |Set'(Var'(VarBound(_,major,minor)), exp) -> (generate consts fvars exp) ^ "\n"^ "mov rbx, qword [rbp + 8*2]" ^ "\n" ^ "mov rbx, qword [rbp + 8*" ^ (string_of_int major) ^ "]" ^ "\n" ^
  "mov qword [rbx + 8*" ^ (string_of_int minor) ^ "], rax"^  "\n"^ "mov rax, sob_void"
  |Set'(Var'(VarFree(v)), exp) -> (generate consts fvars exp) ^ "\n"^ "mov qword [fvar_tbl+" ^ string_of_int (List.assoc v fvars) ^"], rax" ^"\n" ^ "mov rax, sob_void"
  |Def'(Var'(VarFree(v)), exp)-> (generate consts fvars exp) ^ "\n"^ "mov qword [fvar_tbl+" ^ string_of_int (List.assoc v fvars) ^"], rax" ^"\n" ^ "mov rax, sob_void"
  | Or'(expr_list)-> let all_orrs = List.fold_left (fun accList curexp -> accList ^ (generate consts fvars curexp) ^ "cmp rax, SOB_FALSE_ADDRESS \n jne Lexit" ^ (string_of_int label_index.index)) "" expr_list 
  in let fin_str = all_orrs ^ "\nLexit" ^(string_of_int label_index.index) ^ ":" in let () = label_index.index <- label_index.index + 1 in fin_str 
  | LambdaSimple'(params, expr)-> let generated_body = (generate consts fvars expr) in generate_lambda_simple generated_body (string_of_int label_index.index)
  (*| LambdaOpt'(params, optional, expr)->
  | Applic'(closure, args)-> 
  | ApplicTP'(closure, args)->*)
  |_-> "";;
end;;

