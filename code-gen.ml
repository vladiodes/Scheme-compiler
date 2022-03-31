#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
(*Tom*)

  let get_bytes_length sexpr = match sexpr with 
        | ScmVoid -> 1
        | ScmNil -> 1
        | ScmBoolean(_) -> 2
        | ScmChar(_) -> 2
        | ScmString(str) -> 9 + (String.length str)
        | ScmSymbol(str) -> 9
        | ScmNumber(num) -> let output = match num with
                              | ScmRational(_,_) -> 17

                              | ScmReal(_) -> 9 in output
        | ScmVector(lst) -> 9 + ((List.length lst)*8)
        | ScmPair(_,_) -> 17
  
  let rec make_constants  ast  = match ast with 
    | ScmConst'(sexpr) -> [sexpr]
    | ScmVar' (var) -> []
    | ScmBox' (var) -> []
    | ScmBoxGet' (var) -> []
    | ScmBoxSet'(var, expr') -> make_constants expr'
    | ScmIf' (test, dit, dif) -> (make_constants test) @ (make_constants dit) @ (make_constants dif)
    | ScmSeq' (exprs) -> List.fold_left (fun cur_lst cur_exp -> cur_lst @ (make_constants cur_exp)) [] exprs
    | ScmSet' (var, expr') -> make_constants expr'
    | ScmDef' (var, expr') -> make_constants expr'
    | ScmOr' (exprs) -> List.fold_left (fun cur_lst cur_exp -> cur_lst @ (make_constants cur_exp)) [] exprs
    | ScmLambdaSimple' (params, expr) -> make_constants expr 
    | ScmLambdaOpt' (params, last_param, expr) -> make_constants expr 
    | ScmApplic' (expr, exprs) -> let lst = List.fold_left (fun cur_lst cur_exp -> cur_lst @ (make_constants cur_exp)) [] exprs in
                                  lst @ (make_constants expr)
    | ScmApplicTP' (expr, exprs) -> let lst = List.fold_left (fun cur_lst cur_exp -> cur_lst @ (make_constants cur_exp)) [] exprs in
                                  lst @ (make_constants expr) 
  

  let rec list_mem_const c lst = match lst with 
    | [] -> false
    | hd::tail -> sexpr_eq hd c || list_mem_const c tail 

  let uniq_cons x xs = if list_mem_const x xs then xs else x :: xs
  let remove_from_right xs = List.fold_right uniq_cons xs []


  let cons_uniq xs x = if list_mem_const x xs then xs else x :: xs
  let remove_from_left lst = List.rev (List.fold_left cons_uniq [] lst)
  
  
  let rec make_list_with_3_tuple consts_lst= match consts_lst with
    | [] -> []
    | hd::tail -> [(hd,(0,""))] @ (make_list_with_3_tuple tail)
      

  let rec get_off lst sexpr = match lst with
    | [] -> -1 
    | (hd,(off, _))::tail -> if sexpr_eq hd sexpr then off else get_off tail sexpr

  let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

  let rec get_asm_str sexpr beginning_lst = match sexpr with  
        | ScmVoid -> "db T_VOID"
        | ScmNil-> "db T_NIL"
        | ScmBoolean(false)-> "db T_BOOL, 0"
        | ScmBoolean(true)-> "db T_BOOL, 1"

        | ScmChar(ch)-> "MAKE_LITERAL_CHAR("^(string_of_int (Char.code ch))^")"
        | ScmString(str)-> let str_chars_lst = explode str in
                           let params_str = List.fold_left (fun acc cur -> acc^(string_of_int (Char.code cur))^",") "" str_chars_lst in
                            "MAKE_LITERAL_STRING "^params_str^"\n"  
        | ScmSymbol(str)->  let str_off = get_off beginning_lst (ScmString str) in 
                            "MAKE_LITERAL_SYMBOL(const_tbl+"^string_of_int str_off^")"
        | ScmNumber (ScmRational (num,deno)) -> "MAKE_LITERAL_RATIONAL(" ^ (string_of_int num) ^ ","^ (string_of_int deno) ^")"

        | ScmNumber (ScmReal (num)) -> "MAKE_LITERAL_FLOAT(" ^ (string_of_float num)^ ")"
        | ScmVector(sexpr_lst) -> let pointers_str = List.fold_left (fun acc cur -> acc^"const_tbl+"^(string_of_int (get_off beginning_lst cur))^",") "" sexpr_lst in
                                  let output = "MAKE_LITERAL_VECTOR "^pointers_str in output
        | ScmPair(car, cdr)-> let car_off = get_off beginning_lst car in 
                              let cdr_off = get_off beginning_lst cdr in 
                              "MAKE_LITERAL_PAIR(const_tbl+"^string_of_int car_off^", const_tbl+"^string_of_int cdr_off^")"
  let rec set_str_asm const_tbl beginnig_lst = match const_tbl with
    | [] -> []
    | (hd,(off,_)) as h::tail -> [(hd, (off,get_asm_str hd beginnig_lst))] @ set_str_asm tail (beginnig_lst @ [h])
    
    
  let rec make_constants_extansion sexpr = match sexpr with 
    | (ScmSymbol(str)) as sym-> [ScmString str] @ [sym]
    | (ScmPair(car, cdr)) as p->(make_constants_extansion car) @  (make_constants_extansion cdr) @ [p]
    | (ScmVector(sexprs)) ->(List.fold_left (fun cur_lst cur_exp -> cur_lst @ (make_constants_extansion cur_exp)) [] sexprs) @ [sexpr]
    | (ScmVoid) as v ->[v]
    | (ScmNil) as n ->[n]
    | (ScmBoolean(_)) as b ->[b]
    | (x) -> [x]

  let rec set_offsets consts_lst off= match consts_lst with
    | [] -> []
    | hd::tail -> let cur_const = (hd, (off,(""))) in 
      [cur_const] @ (set_offsets tail (off+ get_bytes_length hd))

  let make_consts_tbl asts = 
    (*list of all consts *)
    let consts_list =  List.fold_left (fun cur_lst cur_exp -> cur_lst @ (make_constants cur_exp)) [] asts in
    (* remove duplicates *)
    let consts_list = remove_from_left consts_list in 
    (* default values of consts table *)
    let default_values = [ScmVoid;ScmNil;ScmBoolean(false); ScmBoolean(true)] in
    let consts_list = default_values @ consts_list in
    let const_lst_with_sub_consts = List.fold_left (fun cur_lst cur_exp -> cur_lst @ (make_constants_extansion cur_exp)) [] consts_list in
    let const_lst_with_sub_consts = remove_from_left const_lst_with_sub_consts in
    let const_tbl_with_offsets =  set_offsets const_lst_with_sub_consts 0 in  
    let const_tbl_with_offsets = set_str_asm const_tbl_with_offsets [] in const_tbl_with_offsets

  let make_fvars_tbl asts = 
    let rec extract_free_from_var var = match var with
      | VarFree(var) -> [var]
      | _ -> []

    and make_fvars_tbl_single_ast ast = match ast with
      | ScmConst'(sexpr) -> []
      | ScmVar'(var) -> extract_free_from_var var
      | ScmBox'(var) -> extract_free_from_var var
      | ScmBoxGet'(var) -> extract_free_from_var var
      | ScmBoxSet'(var,expr) -> (extract_free_from_var var)@(make_fvars_tbl_single_ast expr)
      | ScmIf'(test,dit,dif) -> let lst1 = make_fvars_tbl_single_ast test in
                                let lst2 = make_fvars_tbl_single_ast dit in
                                let lst3 = make_fvars_tbl_single_ast dif in
                                lst1@lst2@lst3
      | ScmSeq'(expr_lst) -> List.fold_left (fun acc cur -> acc@make_fvars_tbl_single_ast cur) [] expr_lst
      | ScmSet'(var,expr) -> (extract_free_from_var var) @ (make_fvars_tbl_single_ast expr)
      | ScmDef'(var,expr) -> (extract_free_from_var var) @ (make_fvars_tbl_single_ast expr)
      | ScmOr'(expr_lst) -> List.fold_left (fun acc cur -> acc@make_fvars_tbl_single_ast cur) [] expr_lst
      | ScmLambdaSimple'(_,expr) -> make_fvars_tbl_single_ast expr
      | ScmLambdaOpt'(_,_,expr) -> make_fvars_tbl_single_ast expr
      | ScmApplic'(expr,expr_lst) -> let first = make_fvars_tbl_single_ast expr in
                                     let rest = List.fold_left (fun acc cur -> acc@make_fvars_tbl_single_ast cur) [] expr_lst in
                                     first@rest
      | ScmApplicTP'(expr,expr_lst) -> let first = make_fvars_tbl_single_ast expr in
                                       let rest = List.fold_left (fun acc cur -> acc@make_fvars_tbl_single_ast cur) [] expr_lst in
                                       first@rest

    and remove_elem_from_list elem lst =
         let rec helper l acc = match l with
           | [] -> List.rev acc
           | x::xs when (x=elem) -> helper xs acc
           | x::xs -> helper xs (x::acc)
         in helper lst []

    and remove_duplicates lst =
         let rec helper l acc = match l with
           | [] -> List.rev acc
           | x :: xs -> helper (remove_elem_from_list x xs) (x::acc)
         in helper lst []

    and index_free_vars index vars_lst acc = match vars_lst with
        | [] -> acc
        | var::vars -> index_free_vars (index+1) vars (acc@[(var,index*8)])
    
    in index_free_vars 0 (remove_duplicates (["boolean?"; "flonum?"; "rational?"; "pair?"; "null?"; "char?"; "string?"; "procedure?"; "symbol?";
               "string-length"; "string-ref"; "string-set!"; "make-string"; "symbol->string"; "char->integer";
               "integer->char"; "exact->inexact"; "eq?"; "+"; "*"; "/"; "="; "<"; "numerator"; "denominator";
               "gcd"; "apply"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"]@ (List.fold_left (fun acc cur -> acc@make_fvars_tbl_single_ast cur)) [] asts)
              ) [];;

  let inc_index_ref index_ref = (!index_ref,(index_ref:=!index_ref+1));;

  let idx_ref = ref 0;;

    (*  rax has new env pointer
        rbx has the prev env
        rcx has num of vectors copied to new env
        rdx holds how much vectors should be copied*)
    let copy_prev_env index_str = 
      let output = "extend_prev_env"^index_str^":\n" in
      let output = output^ "cmp rcx, rdx\n" in
      let output = output^ "jge extend_prev_env_exit"^index_str^"\n" in
      let output = output^ "mov rsi, [rbx+WORD_SIZE*rcx] ;rsi holds the vector that should be copied to the new env \n" in
      let output = output^ "mov [rax+WORD_SIZE+rcx*WORD_SIZE], rsi ;skipping the first floor - params will be copeid there \n " in
      let output = output^ "inc rcx\n jmp extend_prev_env"^index_str^"\n" in
      let output = output^ "extend_prev_env_exit"^index_str^":\n" in
      output;;

  (*
    rax has pointer to new env
    rbx has the pointer to the prev_param vector (after malloc)
    rcx holds num of params copied 
    rdx holds num of params in prev lambda 
  *)
    let copy_prev_params_to_env index_str num_params =
      let output = "mov rdx,qword "^(string_of_int num_params)^"\n" in
      let output = output^ "mov rcx,0\n" in
      let output = output^ "mov rsi,rdx\n" in
      let output = output^ "shl rsi,3\n" in
      let output = output^ "MALLOC rbx, rsi ;memory for params from stack that should be copied to new env \n" in
      let output = output^ "copy_prev_params"^index_str^":\n" in
      let output = output^ "cmp rcx, rdx\n" in
      let output = output^ "jge copy_prev_params_end"^index_str^"\n" in
      let output = output^ "mov rsi, qword [rbp + WORD_SIZE*(4+rcx)] ;rsi is the RCXth param that we copy\n" in
      let output = output^ "mov [rbx+WORD_SIZE*rcx],rsi ; putting the param in its place\n" in
      let output = output^ "inc rcx\n" in
      let output = output^ "jmp copy_prev_params"^index_str^"\n" in 
      let output = output^ "copy_prev_params_end"^index_str^":\n" in
      let output = output^ "mov [rax], rbx; rax is the new closure\n" in
      output;;

  (*
    rsi holds the expected number of args to the lambda (excluding optional)
    rcx holds number of args pushed onto the stack during applic
    loops and generates a list from all the optional args.
  *)
    let fix_stack_after_magic index_str params_length =
      let fix_stack = "mov rsi,"^(string_of_int params_length)^"; actual args lambda expecting \n" in
      let fix_stack = fix_stack^"mov rcx, qword [rbp + WORD_SIZE *3]; rcx holds number of params pushed w/o magic \n" in
      let fix_stack = fix_stack^"mov rdx, SOB_NIL_ADDRESS ;the last value of the proper list\n" in 
      let fix_stack = fix_stack^"fix_stack"^index_str^":\n" in
      let fix_stack = fix_stack^ "cmp rsi,rcx\n" in
      let fix_stack = fix_stack^ "je fix_stack_finish"^index_str^"\n" in
      let fix_stack = fix_stack^ "dec rcx\n" in
      let fix_stack = fix_stack^ "mov rbx, qword [rbp+WORD_SIZE*(4+rcx)] ; getting next opt param\n" in
      let fix_stack = fix_stack^ "MAKE_PAIR(rax,rbx,rdx)\n" in
      let fix_stack = fix_stack^ "mov rdx,rax ;preparing next iteration \n" in
      let fix_stack = fix_stack^ "jmp fix_stack"^index_str^"\n" in
      let fix_stack = fix_stack^ "fix_stack_finish"^index_str^":\n" in
      let fix_stack = fix_stack^ "mov [rbp+WORD_SIZE*(4+rsi)],rdx\n" in
      fix_stack;;

  let generate consts fvars e = 
  let rec generate_helper consts fvars e index_ref env_depth params_length = match e with
    | ScmSeq'(exprs) -> List.fold_left (fun cur_lst cur_exp -> cur_lst ^ (generate_helper consts fvars cur_exp index_ref env_depth params_length) ^ "\n") "" exprs
    | ScmIf'(test,dit,dif) -> 
                              let (lbl_index,_) = inc_index_ref index_ref  in
                              let lbl_index_str = string_of_int lbl_index in
                              let test_str = generate_helper consts fvars test index_ref env_depth params_length in
                              let dit_str = generate_helper consts fvars dit index_ref env_depth params_length in
                              let dif_str = generate_helper consts fvars dif index_ref env_depth params_length in
                              let output_str = test_str^"\n"^"cmp rax, SOB_FALSE_ADDRESS\n" in
                              let output_str = output_str^"je "^"Lelse"^lbl_index_str^"\n" in
                              let output_str = output_str^dit_str^"\n" in
                              let output_str = output_str^"jmp "^"Lexit"^lbl_index_str^"\n" in
                              let output_str = output_str^"Lelse"^lbl_index_str^":\n" in
                              let output_str = output_str^dif_str^"\n" in
                              let output_str = output_str^"Lexit"^lbl_index_str^":\n" in
                              output_str
    | ScmOr'(expr_lst) -> let (lbl_index,_) = inc_index_ref index_ref  in
                          let lbl_index_str = string_of_int lbl_index in
                          let single_exp_gen expr = 
                                let expr_str = generate_helper consts fvars expr index_ref env_depth params_length in
                                let output_str = expr_str^"\n"^"cmp rax, SOB_FALSE_ADDRESS\n" in
                                let output_str = output_str^"jne "^"Lexit"^lbl_index_str^"\n" in output_str in
                          let output_str = List.fold_left (fun acc cur -> acc^(single_exp_gen cur)) "" expr_lst in
                          let output_str = output_str^"\n Lexit"^lbl_index_str^":\n" in
                          output_str
    | ScmConst'(const) -> let const_row = List.find (fun (c,(_,_)) -> sexpr_eq const c) consts in
                          let offset = (fun (_, (off, _)) -> off) const_row in "mov rax, const_tbl+"^(string_of_int offset)^"\n"
    
    | ScmVar'(var) -> let output =match var with 
          | VarFree(v) -> let fvars_row = List.find (fun (c,off) ->  v=c ) fvars in
                          let offset = (fun (_, off) -> off) fvars_row in "mov rax, qword [fvar_tbl+"^(string_of_int offset)^"]\n"
          | VarBound(_,major,minor) -> let str = "mov rax, qword [rbp + 8*2]
                                          mov rax, qword [rax+WORD_SIZE*"^(string_of_int major)^"]
                                          mov rax, qword [rax+WORD_SIZE*"^(string_of_int minor)^"]\n" in str
          | VarParam(_, minor) -> let str = "mov rax, qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")]\n" in str
          in output

    | ScmSet'(var,value) -> let output = match var with
                            | VarFree(v) -> let expr_str = generate_helper consts fvars value index_ref env_depth params_length in
                                            let free_row = List.find (fun (f,_) -> v=f) fvars in
                                            let offset = (fun (_,off) -> off) free_row in
                                            let offset = string_of_int offset in
                                            let str = expr_str^"mov qword [fvar_tbl+"^offset^"], rax \n" in
                                            let str = str^"mov rax, SOB_VOID_ADDRESS \n" in  str
                            | VarBound(_,major,minor) -> let expr_str = generate_helper consts fvars value index_ref env_depth params_length in
                                                         let str =  "mov rbx, qword [rbp + WORD_SIZE * 2]
                                                                     mov rbx, qword [rbx + WORD_SIZE * " ^ (string_of_int major) ^ "]
                                                                     mov qword [rbx + WORD_SIZE * " ^ (string_of_int minor) ^ "], rax
                                                                     mov rax, SOB_VOID_ADDRESS\n" in 
                                                         let str = expr_str ^ str in str

                            | VarParam(_, minor) -> let expr_str = generate_helper consts fvars value index_ref env_depth params_length in
                                                    let str = "mov qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")], rax
                                                    mov rax, SOB_VOID_ADDRESS\n" in let str = expr_str ^ str in str in output


    | ScmDef'(var,expr) -> let output = match var with
                            | VarFree(v) -> let expr_str = generate_helper consts fvars expr index_ref env_depth params_length in
                                            let free_row = List.find (fun (f,_) -> v=f) fvars in
                                            let offset = (fun (_,off) -> off) free_row in
                                            let offset = string_of_int offset in
                                            let str = expr_str^"mov qword [fvar_tbl+"^offset^"], rax \n" in
                                            let str = str^"mov rax, SOB_VOID_ADDRESS \n" in
                                            str
                            | _ -> raise X_not_yet_implemented in output


    | ScmBox'(var') -> let expr_str = generate_helper consts fvars (ScmVar' var') index_ref env_depth params_length in
                       let str = "MALLOC rbx, WORD_SIZE
                                  mov [rbx], rax
                                  mov rax, rbx\n" in let str = expr_str ^ str in str


    | ScmBoxGet'(var') -> let expr_str = generate_helper consts fvars (ScmVar' var') index_ref env_depth params_length in
                          let str = "mov rax, qword [rax]\n" in
                          let str = expr_str ^ str in str

    | ScmBoxSet'(var',expr') -> let expr_str = generate_helper consts fvars expr' index_ref env_depth params_length in 
                                let var_str = generate_helper consts fvars (ScmVar' var') index_ref env_depth params_length in 
                                let str = "push rax
                                          " ^ var_str ^ "
                                          pop qword [rax]
                                          mov rax, SOB_VOID_ADDRESS\n" in let str = expr_str ^ str in str


    | ScmLambdaSimple'(params,body) -> let new_env_size = env_depth+1 in 
                                       let (lbl_index,_) = inc_index_ref index_ref  in
                                       let lbl_index_str = string_of_int lbl_index in
                                       let extend_env = "MALLOC rax,WORD_SIZE*"^(string_of_int new_env_size)^"; memory for new env\n" in
                                       let extend_env = extend_env^"mov rcx, 0 ; will hold number of envs copied \n" in
                                       let extend_env = extend_env^"mov rbx, qword [rbp + 2*WORD_SIZE] ;old env \n" in
                                       let extend_env = extend_env^"mov rdx, "^(string_of_int env_depth)^" ; holds how much envs to copy\n" in
                                       let extend_env = extend_env^copy_prev_env lbl_index_str in
                                       let copy_prev_params = copy_prev_params_to_env lbl_index_str params_length in
                                       let allocate_closure_skip_body = "MAKE_CLOSURE (rbx,rax,Lcode"^lbl_index_str^") ;"^(string_of_expr' e)^"\n" in
                                       let allocate_closure_skip_body = allocate_closure_skip_body^"mov rax,rbx\n" in
                                       let allocate_closure_skip_body = allocate_closure_skip_body^"jmp Lcont"^lbl_index_str^"\n" in
                                       let body_str = generate_helper consts fvars body index_ref new_env_size (List.length params) in
                                       let body_str = "Lcode"^lbl_index_str^":
                                                       push rbp
                                                       mov rbp, rsp
                                                       "^body_str^
                                                       "leave
                                                        ret
                                                        Lcont"^lbl_index_str^":\n" in
                                      (extend_env^copy_prev_params^allocate_closure_skip_body^body_str)

    | ScmLambdaOpt'(params,op_param,body) -> let new_env_size = env_depth+1 in 
                                       let (lbl_index,_) = inc_index_ref index_ref  in
                                       let lbl_index_str = string_of_int lbl_index in
                                       let extend_env = "MALLOC rax,WORD_SIZE*"^(string_of_int new_env_size)^"; memory for new env\n" in
                                       let extend_env = extend_env^"mov rcx, 0 ; will hold number of envs copied \n" in
                                       let extend_env = extend_env^"mov rbx, qword [rbp + 2*WORD_SIZE] ;old env \n" in
                                       let extend_env = extend_env^"mov rdx, "^(string_of_int env_depth)^" ; holds how much envs to copy\n" in
                                       let extend_env = extend_env^copy_prev_env lbl_index_str in
                                       let copy_prev_params = copy_prev_params_to_env lbl_index_str params_length in
                                       let allocate_closure_skip_body = "MAKE_CLOSURE (rbx,rax,Lcode"^lbl_index_str^");"^(string_of_expr' e)^"\n" in
                                       let allocate_closure_skip_body = allocate_closure_skip_body^"mov rax,rbx\n" in
                                       let allocate_closure_skip_body = allocate_closure_skip_body^"jmp Lcont"^lbl_index_str^"\n" in
                                       let fix_stack = fix_stack_after_magic lbl_index_str (List.length params) in
                                       let body_str = generate_helper consts fvars body index_ref new_env_size ((List.length params) + 1) in
                                       let body_str = "Lcode"^lbl_index_str^":

                                                       push rbp
                                                       mov rbp, rsp
                                                       "^fix_stack^
                                                         body_str^
                                                       "leave
                                                        ret
                                                        Lcont"^lbl_index_str^":\n" in
                                      (extend_env^copy_prev_params^allocate_closure_skip_body^body_str)

    | ScmApplic'(proc,arg_lst) -> let one_arg_str arg = 
                                        let arg_str = generate_helper consts fvars arg index_ref env_depth params_length in
                                        let output = arg_str^"\n push rax\n" in
                                        output in
                                  let all_args_str = List.fold_right (fun cur acc -> acc^(one_arg_str cur)) arg_lst "" in
                                  let lst_size = List.length arg_lst in
                                  let lst_size = string_of_int lst_size in
                                  let output = all_args_str^"push qword "^ lst_size^ "\n" in
                                  let proc_str = generate_helper consts fvars proc index_ref env_depth params_length in
                                  let output = output^ proc_str^"\n" in
                                  let output = output^ "call verify_closure\n" in
                                  let output = output^ "CLOSURE_ENV rbx,rax\n" in
                                  let output = output^ "push rbx\n" in
                                  let output = output^ "CLOSURE_CODE rbx,rax\n" in
                                  let output = output^ "call rbx\n" in
                                  let output = output^ "add rsp, WORD_SIZE*1
                                                        pop rbx
                                                        inc rbx ;take care of magic
                                                        lea rsp, [rsp+WORD_SIZE*rbx]\n" in 
                                  "push qword SOB_NIL_ADDRESS ;magic! \n"^output
    
    | ScmApplicTP'(proc,args) -> let one_arg_str arg = 
                                        let arg_str = generate_helper consts fvars arg index_ref env_depth params_length in
                                        let output = arg_str^"\n push rax\n" in
                                        output in
                                  let all_args_str = List.fold_right (fun cur acc -> acc^(one_arg_str cur)) args "" in
                                  let lst_size = List.length args in
                                  let lst_size = string_of_int lst_size in
                                  let output = all_args_str^"push qword "^ lst_size^ "\n" in
                                  let proc_str = generate_helper consts fvars proc index_ref env_depth params_length in
                                  let output = output^ proc_str^"\n" in
                                  let output = output^ "call verify_closure\n" in
                                  let output = output^ "CLOSURE_ENV rbx,rax\n" in
                                  let output = output^ "push rbx\n" in
                                  let output = output ^ "push qword[rbp + WORD_SIZE * 1] ; old return address \n" in
                                  let output = output ^ "push qword [rbp] \n" in
                                  let output = output ^ "mov rcx, PARAM_COUNT \n" in
                                  let output = output ^ "SHIFT_FRAME (" ^ lst_size ^ " + 5) \n" in
                                  
                                  let output = output ^ "add rcx, 5 \n" in
                                  let output = output ^ "shl rcx, 3 \n" in
                                  let output = output ^ "add rsp, rcx \n" in
                                  let output = output^ "pop rbp \n" in

                                  let output = output^ "CLOSURE_CODE rbx,rax\n" in
                                  let output = output^ "jmp rbx\n" in 
                                  
                                  let output = "push qword SOB_NIL_ADDRESS ;magictp! \n" ^ output in output



                                


    in generate_helper consts fvars e idx_ref 0 0;;
                            

end;;
