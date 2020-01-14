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
  |Sexpr(String(str)) -> ( (const, (offset, "MAKE_LITERAL_STRING \""^ str ^"\"")), (String.length str) + 9) (*to check!*)
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
  |Sexpr(Char(c)) -> ( (const, (offset, "MAKE_LITERAL_CHAR('"^ (Char.escaped c) ^"')")), 2)
  |Sexpr(String(str)) -> ( (const, (offset, "MAKE_LITERAL_STRING \""^ str ^"\"")), (String.length str) + 9) (*to check!*)
  |Sexpr(Symbol(str)) -> ( (const, (offset, "MAKE_LITERAL_SYMBOL(const_tbl+ "^ (string_of_int (get_const_address_iter_2 table (Sexpr(String(str))))) ^")")), 9)
  |Sexpr(Pair(sexpr1, sexpr2)) ->  ( (const, (offset, " MAKE_LITERAL_PAIR(const_tbl+ "^ (string_of_int (get_const_address_iter_2 table (Sexpr(sexpr1)))) ^", const_tbl+" ^ (string_of_int (get_const_address_iter_2 table (Sexpr(sexpr2)))) ^")")), 17)
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
  | ApplicTP'(closure, params)-> ApplicTP'(rename_reffs closure indx, (List.map (fun exp -> rename_reffs exp indx) params)) 
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
  | ApplicTP'(closure, params)-> ApplicTP'(build_dictionary_and_remove_tagges closure , (List.map (fun exp -> build_dictionary_and_remove_tagges exp ) params)) 
  | _ -> exp';;

let rename_ast asts =
  let (asts_renamed,_) =  List.fold_left (fun (accList,indx) exp' -> (accList @ [(rename_reffs exp' indx)] , indx +1 )) ([],0) asts in 
  asts_renamed;;
let ast_without_tagggedSexpr asts = List.fold_left (fun accList curr -> accList @ [build_dictionary_and_remove_tagges curr]) [] asts;;  


  let make_consts_tbl asts = 
  let must_const = [Void ;Sexpr(Nil); Sexpr(Bool false) ; Sexpr(Bool true)] in
  let list_of_consts = List.flatten (List.map make_list_of_all_consts asts) in
  let extended_list = must_const @ List.flatten (List.map extend_consts_table list_of_consts) in
  let reduced = reduce_list extended_list in
  let table_1 = build_consts_table reduced in build_consts_table_iter_2 table_1;; 

  let check s= 
  let str = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s)) in
                             str;;

let exists_str curr_const consts_list = 
  List.fold_left (fun acc curr -> if (curr = curr_const) then true else acc) false consts_list;;
  
let reduce_list_str l = 
  List.fold_left (fun  acc curr -> if(exists_str curr acc) then acc else acc@[curr]) [] l;;

let primitive_names = 
  ["boolean?"; "float?"; "integer?"; "pair?"; "null?"; "char?"; "string?"; "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string"; "symbol->string"; "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "=";"car";  "cdr"; "cons"; "set-car!"; "set-cdr!";  "apply" (* you can add yours here *)];;


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
let (fvars_table,_) = List.fold_left (fun (acclist,indx) str -> ((acclist @ [(str,indx)]),( indx + 8))) ([],0) fvars_set in fvars_table;;

let make_fvars_tbl asts = gen_fvars_table asts;;


let get_address_in_const_table constant consts_table =  "const_tbl+" ^ (string_of_int (get_const_address consts_table constant));;



type mutable_int = {mutable index:int};; 
let label_index = {index = 0};;

let generate_lambda str_index= 
 "mov rbx, [rbp + 8*2] ;;rbx = address of env
  mov rcx, 1 ;;counter for size of env
  cmp qword rbx, SOB_NIL_ADDRESS ;;just for the first env 
  je end_count_env_length" ^ str_index ^"
count_env_length" ^ str_index ^":
    add rcx, 1
    add rbx, 8 
    cmp qword [rbx], SOB_NIL_ADDRESS
    je end_count_env_length" ^ str_index ^"
    jmp count_env_length" ^ str_index ^"
end_count_env_length" ^ str_index ^": 
    push rcx
    add rcx,1 ;;size of extent env 
    shl rcx, 3 ;;mul rcx*8
    MALLOC rax, rcx 
    pop rcx ;;old env size 
    mov rbx, [rbp + 8*2] ;;rbx = address of old env 
    ;;extent first env
    cmp rcx, 1
    je extent_first_env" ^ str_index ^" 
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

extent_first_env"^ str_index ^":
    mov qword [rax+8], SOB_NIL_ADDRESS

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
copy_params" ^ str_index ^":
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
    jmp copy_params" ^ str_index ^"
end_copy_params" ^ str_index ^":
    mov rbx, rax 
    MAKE_CLOSURE(rax, rbx ,Lcode" ^ str_index ^") 
    jmp Lcont" ^ str_index ;;

let genarate_simple_body generated_body str_index =
"\nLcode" ^ str_index ^":
    push rbp
    mov rbp, rsp \n"^ generated_body ^
 "\nleave
    ret 
Lcont" ^ str_index ^":";;

let genarate_opt_body generated_body str_index num_of_args=
"\nLcode" ^ str_index ^":
    mov rcx, [rsp + 2*8] ;; number of argumants
    mov rdx, " ^ num_of_args ^" 
    mov rsi, 2 
    add rsi, rcx ;;last argumant
    shl rsi, 3 ;;mul by 8
    add rsi ,rsp ;;rsi is the top the stack befor magic 
    sub rcx, rdx ;;number of iteration
    cmp rcx, 0 ;;empty opt
    je put_nil" ^ str_index^"\n
    mov rbx, qword [rsi]
    MAKE_PAIR(rax ,rbx ,SOB_NIL_ADDRESS)
    mov rdi, 1
    sub rsi, 8 ;;to go down by one argumant 
  generate_opt_list" ^ str_index ^ ":
    cmp rdi, rcx
    je end_generate_opt_list" ^ str_index ^ " 
    mov rbx, qword [rsi] ;;current argumant
    mov rdx, rax ;;ponter to previus pair
    MAKE_PAIR(rax ,rbx ,rdx)
    inc rdi
    sub rsi, 8 ;;to go down by one argumant 
    jmp generate_opt_list" ^ str_index ^ "
  end_generate_opt_list" ^ str_index ^ ":
    mov rdx, " ^ num_of_args ^" 
    mov rcx, 3 ;;until first args +1 for the new argument that we added
    add rcx, rdx ;;plus number of argumants
    shl rcx, 3 ;;multiply by 8
    add rcx, rsp ;;make it the pointer to the first optional arg
    mov qword [rcx], rax ;; list of optionals
    inc rdx ;;new number of args
    mov rcx, qword [rsp + 2*8] ;; previous number of args
    mov qword [rsp + 2*8], rdx ;; change number of argumant to be real number of argoumants
    ;;dest = (prev number of args - cur args) * 8 + rsp 
    mov rdi, rcx ;;prev number of args 
    sub rdi, rdx ;;curr
    shl rdi, 3 
    add rdi, rsp ;;dest
    ;;src = rsp
    mov rsi, rsp
    ;;size 
    add rdx, 3
    shl rdx, 3
    call memmove 
    mov rsp, rax 
    jmp body_start" ^ str_index ^"
  put_nil" ^ str_index^":
    add rsi, 8 ;; get to magic
    mov qword [rsi], SOB_NIL_ADDRESS
  body_start" ^ str_index ^":
    push rbp
    mov rbp, rsp \n"^ generated_body ^
 "\nleave
    ret 
Lcont" ^ str_index ^":";;

let magic = "push qword 12345678\n";;
let call_function_and_return =   
   "cmp byte [rax], T_CLOSURE \n
   jne L_total_exit
   CLOSURE_ENV rbx, rax
   push rbx 
   CLOSURE_CODE rbx, rax
   call rbx
   ;;after returning 
   add rsp, 8 ;;pop env
   pop rbx ;;rbx = number of args
   shl rbx, 3 ;; rbx = rbx*8
   add rsp, rbx ;;pop args
   add rsp, 8 ;;pop magic";;

  let rec generate consts fvars e = match e with
  | Const'(constant)->  "mov rax, " ^ (get_address_in_const_table constant consts)
  | Var'(VarParam(_,minor)) -> "mov rax, qword [rbp + 8 * (4 + " ^ string_of_int minor ^ ")]"
  | Var'(VarBound(_,major,minor)) -> "mov rax, qword [rbp + 8*2]\nmov rax, qword [rax + 8*"^ (string_of_int major) ^ "] \nmov rax, qword [rax + 8*" ^(string_of_int minor) ^ "]"
  | Var'(VarFree(name)) -> "mov rax, qword [fvar_tbl+" ^  (string_of_int (List.assoc name fvars))^"]" 
  | Box'(VarParam(var,minor)) -> (generate consts fvars (Var'(VarParam(var,minor)))) ^ "\nMALLOC rbx, 8\n" ^ "mov [rbx], rax\n" ^ "mov [rbp + 8 * (4 + " ^ string_of_int minor ^ ")], rbx"
  | BoxGet'(v)-> (generate consts fvars (Var'(v))) ^ "\n" ^ "mov rax, qword [rax]"
  | BoxSet'(v, exp)->  (generate consts fvars exp) ^ "\npush rax\n" ^ (generate consts fvars (Var'(v))) ^ "\npop qword [rax] \nmov rax, SOB_VOID_ADDRESS"
  | If'(test, dit, dif) -> let test = (generate consts fvars test) in let dit_s = (generate consts fvars dit) in let dif_s = (generate consts fvars dif) in
  let str =  test ^ "\n" ^ "cmp rax, SOB_FALSE_ADDRESS" ^ "\n" ^ "je Lelse" ^ (string_of_int label_index.index)^  "\n"
  ^ dit_s ^"\n" ^ "jmp Lexit" ^ (string_of_int label_index.index) ^ "\n" ^ "Lelse" ^ (string_of_int label_index.index) ^":\n" ^ dif_s
  ^ "\nLexit" ^(string_of_int label_index.index) ^ ":" in let () = label_index.index <- label_index.index + 1 in str 
  | Seq'(expr_list)-> List.fold_left (fun acc curr ->  acc ^ "\n" ^ (generate consts fvars curr)) "" expr_list 
  | Set'(Var'(VarParam(_, minor)), exp)-> (generate consts fvars exp) ^ "\n"^
  "mov qword [rbp + 8*(4+ " ^ (string_of_int minor) ^ ")], rax" ^"\n"^ 
  "mov rax, SOB_VOID_ADDRESS"
  |Set'(Var'(VarBound(_,major,minor)), exp) -> (generate consts fvars exp) ^ "\n"^ "mov rbx, qword [rbp + 8*2]" ^ "\n" ^ "mov rbx, qword [rbp + 8*" ^ (string_of_int major) ^ "]" ^ "\n" ^
  "mov qword [rbx + 8*" ^ (string_of_int minor) ^ "], rax"^  "\n"^ "mov rax, SOB_VOID_ADDRESS"
  |Set'(Var'(VarFree(v)), exp) -> (generate consts fvars exp) ^ "\n"^ "mov qword [fvar_tbl+" ^ string_of_int (List.assoc v fvars) ^"], rax" ^"\n" ^ "mov rax, SOB_VOID_ADDRESS"
  |Def'(Var'(VarFree(v)), exp)-> (generate consts fvars exp) ^ "\n"^ "mov qword [fvar_tbl+" ^ string_of_int (List.assoc v fvars) ^"], rax" ^"\n" ^ "mov rax, SOB_VOID_ADDRESS"
  | Or'(expr_list)-> let all_expr = List.map (generate consts fvars) expr_list in  let all_orrs = List.fold_left (fun accList curr_str -> accList ^ curr_str ^ "\ncmp rax, SOB_FALSE_ADDRESS \njne Lexit" ^ (string_of_int label_index.index) ^"\n") "" all_expr 
  in let fin_str = all_orrs ^ "\nLexit" ^(string_of_int label_index.index) ^ ":" in let () = label_index.index <- label_index.index + 1 in fin_str 
  | LambdaSimple'(params, expr)-> let generated_body = (generate consts fvars expr) in let lambda_code = generate_lambda (string_of_int label_index.index) in let fin_str = lambda_code ^ (genarate_simple_body generated_body (string_of_int label_index.index))
  in let () = label_index.index <- label_index.index + 1 in fin_str
  | LambdaOpt'(params, optional, expr)-> let generated_body = (generate consts fvars expr) in let lambda_code = generate_lambda (string_of_int label_index.index) in let fin_str =  lambda_code ^ (genarate_opt_body generated_body (string_of_int label_index.index) (string_of_int (List.length params)))
   in let () = label_index.index <- label_index.index + 1 in fin_str
  | Applic'(closure, args)->  let push_args_string = List.fold_right (fun curr acc -> acc ^ (generate consts fvars curr)^ "\n"^"push rax\n") args "" in
                               let n = "push " ^(string_of_int (List.length args))^"\n" in 
                               magic ^ push_args_string ^ n ^ (generate consts fvars closure) ^"\n"^ call_function_and_return


  | ApplicTP'(closure, args)-> let push_args_string = List.fold_right (fun curr acc -> acc ^ (generate consts fvars curr)^ "\n"^"push rax\n") args "" in
                               let n = "push " ^(string_of_int (List.length args))^"\n" in 
                               magic ^ push_args_string ^ n ^ (generate consts fvars closure) ^"\n"^
                                "cmp byte [rax], T_CLOSURE \n
                                 jne L_total_exit
                                 CLOSURE_ENV rbx, rax
                                 push rbx ;;push env 
                                 push qword [rbp + 8 * 1] ; old ret addr
                                 ;;fix the stack 
                                 push rax ;;address of closure 
                                 ;;rcx will hold old stack size 
                                 mov rcx, [rbp+3*8] ;;n , rbp the old one 
                                 add rcx, 4 ;; 4 - until first arg
                                 shl rcx, 3 ;;old stack size
                                 add rcx, 8 ;;for the magic  
                                 ;;rdx will hold the size of new stack 
                                 mov rdx, [rsp+3*8] ;;new n 
                                 add rdx, 4 ;; 4 - until first arg
                                 shl rdx, 3 ;;new stack size
                                 add rdx, 8 ;;for the magic  
                                 add rdx, 8 ;;for rbp 
                                 ;;rdi will hold the dest. dest = (old size- new size)*8 + rbp 
                                 mov rdi, rcx 
                                 sub rdi, rdx ;;rdi = rcx - rdx 
                                 add rdi, rbp ;;address of dest 
                                 mov rbp, [rbp]
                                 push rbp ;;old rbp 
                                 ;;rsi will hold the source
                                 mov rsi, rsp 
                                 call memmove
                                 mov rsp, rax ;;address of new stack 
                                 pop rbp ;;old rbp 
                                 pop rax ;;closure 
                                 CLOSURE_CODE rbx, rax
                                 jmp rbx "
                               
|_-> "";;
  
end;;





