(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

 #use "tag-parser.ml";;

 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
 
 type var' = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | ScmConst' of sexpr
   | ScmVar' of var'
   | ScmBox' of var'
   | ScmBoxGet' of var'
   | ScmBoxSet' of var' * expr'
   | ScmIf' of expr' * expr' * expr'
   | ScmSeq' of expr' list
   | ScmSet' of var' * expr'
   | ScmDef' of var' * expr'
   | ScmOr' of expr' list
   | ScmLambdaSimple' of string list * expr'
   | ScmLambdaOpt' of string list * string * expr'
   | ScmApplic' of expr' * (expr' list)
   | ScmApplicTP' of expr' * (expr' list);;
 
 
 let var_eq v1 v2 =
 match v1, v2 with
   | VarFree (name1), VarFree (name2) -> String.equal name1 name2
   | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
     major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
   | VarParam (name1, index1), VarParam (name2, index2) ->
        index1 = index2 && (String.equal name1 name2)
   | _ -> false
 
 let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;
 
 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
   | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
   | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                             (expr'_eq dit1 dit2) &&
                                               (expr'_eq dif1 dif2)
   | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
         list_eq expr'_eq exprs1 exprs2
   | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
         (var_eq var1 var2) && (expr'_eq val1 val2)
   | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
      (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
   | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
   | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
   | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
       (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
   | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
   | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
   | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
   | _ -> false;;
 
 let unannotate_lexical_address = function
 | (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name
 
 let rec unanalyze expr' =
 match expr' with
   | ScmConst' s -> ScmConst(s)
   | ScmVar' var -> unannotate_lexical_address var
   | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
   | ScmBoxGet' var -> unannotate_lexical_address var
   | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
   | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
   | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
   | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
   | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
   | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
   | ScmLambdaSimple' (params, expr') ->
         ScmLambdaSimple (params, unanalyze expr')
   | ScmLambdaOpt'(params, param, expr') ->
         ScmLambdaOpt (params, param, unanalyze expr')
   | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
         ScmApplic (unanalyze expr', List.map unanalyze expr's);;
 
 let string_of_expr' expr' =
     string_of_expr (unanalyze expr');;
 
 module type SEMANTIC_ANALYSIS = sig
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
   val run_semantics : expr -> expr'
 end;; (* end of module type SEMANTIC_ANALYSIS *)
 
 module Semantic_Analysis : SEMANTIC_ANALYSIS = struct
 
   let rec lookup_in_rib name = function
     | [] -> None
     | name' :: rib ->
        if name = name'
        then Some(0)
        else (match (lookup_in_rib name rib) with
              | None -> None
              | Some minor -> Some (minor + 1));;
 
   let rec lookup_in_env name = function
     | [] -> None
     | rib :: env ->
        (match (lookup_in_rib name rib) with
         | None ->
            (match (lookup_in_env name env) with
             | None -> None
             | Some(major, minor) -> Some(major + 1, minor))
         | Some minor -> Some(0, minor));;
 
   let tag_lexical_address_for_var name params env = 
     match (lookup_in_rib name params) with
     | None ->
        (match (lookup_in_env name env) with
         | None -> VarFree name
         | Some(major, minor) -> VarBound(name, major, minor))
     | Some minor -> VarParam(name, minor);;
 
  (* run this first! *)
  let annotate_lexical_addresses pe = 
 
   let rec exp_list_to_expr_tag_list exp_list params env cur_lst = match exp_list with
    | [] -> cur_lst
    | exp::tail -> exp_list_to_expr_tag_list tail params env (cur_lst@[(run exp params env)])
 
    and
    
    run pe params env =
       match pe with
       | ScmConst(sexpr) -> ScmConst'(sexpr)
       | ScmVar(var) -> ScmVar'(tag_lexical_address_for_var var params env)
       | ScmIf(test,dit,dif) -> let test_tag = run test params env in
                                let dit_tag = run dit params env in
                                let dif_tag = run dif params env in
                                ScmIf'(test_tag,dit_tag,dif_tag)
       | ScmSeq(expr_lst) -> let exprs_tag = exp_list_to_expr_tag_list expr_lst params env [] in ScmSeq'(exprs_tag)
       | ScmSet(var_exp,val_exp) -> let var_exp_tag = match (run var_exp params env) with
                                         | ScmVar'(var) -> var
                                         | _ -> raise X_this_should_not_happen in
                                    let val_exp_tag = run val_exp params env in
                                    ScmSet'(var_exp_tag,val_exp_tag)
       | ScmDef(var_exp,val_exp) -> let var_exp_tag = match (run var_exp params env) with
                                         | ScmVar'(var) -> var
                                         | _ -> raise X_this_should_not_happen in
                                    let val_exp_tag = run val_exp params env in
                                    ScmDef'(var_exp_tag,val_exp_tag)
       | ScmOr(expr_lst) -> ScmOr'(exp_list_to_expr_tag_list expr_lst params env [])
       | ScmLambdaSimple(vars_lst,expr) -> ScmLambdaSimple'(vars_lst,run expr vars_lst ([params]@env))
       | ScmLambdaOpt(vars_lst,last_var,expr) -> ScmLambdaOpt'(vars_lst,last_var,run expr (vars_lst@[last_var]) ([params]@env))
       | ScmApplic(expr,expr_lst) -> let expr_tag = run expr params env in
                                     let exprs_tag = exp_list_to_expr_tag_list expr_lst params env [] in
                                     ScmApplic'(expr_tag,exprs_tag)
    in 
    run pe [] [];;
 
 
    let rec rdc_rac s =
     match s with
     | [e] -> ([], e)
     | e :: s ->
        let (rdc, rac) = rdc_rac s
        in (e :: rdc, rac)
     | _ -> raise X_this_should_not_happen;;
   
   (* run this second! *)
   let annotate_tail_calls pe =
    let rec exp_tag_annotatedTP exp_list in_tail curr_lst = match exp_list with
     | [] -> curr_lst
     | exp::tail -> exp_tag_annotatedTP tail in_tail (curr_lst @ [run exp in_tail])
 
 
    and run pe in_tail = match pe with
    | ScmConst'(sexpr) -> ScmConst'(sexpr)
    | ScmVar'(var) -> ScmVar'(var)
    | ScmIf'(test, dit, dif) -> ScmIf'(run test false, run dit in_tail, run dif in_tail)
    | ScmSeq'(exprs_tag) -> 
       let (first_exprs, last_expr) = rdc_rac exprs_tag in
       let first_exprs_tag = exp_tag_annotatedTP first_exprs false [] in
       let last_expr_tag = run last_expr in_tail in
       ScmSeq'(first_exprs_tag @ [last_expr_tag])
    | ScmSet'(var, expr) -> ScmSet'(var, run expr false)
    | ScmDef'(var, expr) -> ScmDef'(var, run expr false)
    | ScmOr'(exprs_tag) -> 
       let (first_exprs, last_expr) = rdc_rac exprs_tag in
       let first_exprs_tag = exp_tag_annotatedTP first_exprs false [] in
       let last_expr_tag = run last_expr in_tail in
       ScmOr'(first_exprs_tag @ [last_expr_tag])
 
 
    | ScmLambdaSimple'(vars, expr) -> ScmLambdaSimple'(vars, run expr true)
    | ScmLambdaOpt'(vars, last_var, expr) -> ScmLambdaOpt'(vars, last_var,run expr true)
    | ScmApplic'(expr, exprs) -> 
     let expr_tag = run expr false in
     let exprs_tag = exp_tag_annotatedTP exprs false [] in
    if in_tail then ScmApplicTP'(expr_tag, exprs_tag) else ScmApplic'(expr_tag, exprs_tag)
    | _ -> pe
    in
    run pe false;;
 
   (* boxing *)
     
   let box_set expr = 
   let rec find_reads name enclosing_lambda body = match body with
       | ScmVar'(var) -> let is_read = match var with
                           | VarFree(_) -> false
                           | VarParam(var,_) -> name=var
                           | VarBound(var,_,_) -> name=var
                         in if is_read then [enclosing_lambda] else []
       | ScmIf'(test,dit,dif) -> let test1 = find_reads name enclosing_lambda test in
                                 let dit1 = find_reads name enclosing_lambda dit in
                                 let dif1 = find_reads name enclosing_lambda dif in
                                 let lst = test1@dit1 in let lst = lst@dif1 in
                                 lst
       | ScmSeq'(expr_lst) -> List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_reads name enclosing_lambda cur_exp)) [] expr_lst
       | ScmSet'(var,expr) -> find_reads name enclosing_lambda expr 
       | ScmDef'(var,expr) -> find_reads name enclosing_lambda expr 
       | ScmOr'(expr_lst) -> List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_reads name enclosing_lambda cur_exp)) [] expr_lst
       | ScmLambdaSimple'(params,body_expr) -> let is_shadow = List.mem name params in
                                             if is_shadow then []
                                             else let output = match (find_reads name body body_expr) with
                                                               | [] -> []
                                                               | _ -> [body] in output
       | ScmLambdaOpt'(params_lst,last_param,body_expr) -> let params = params_lst@[last_param] in
                                                           let is_shadow = List.mem name params in
                                                           if is_shadow then []
                                                           else let output = match (find_reads name body body_expr) with
                                                               | [] -> []
                                                               | _ -> [body] in output
       | ScmApplic'(expr,expr_lst) -> let first = find_reads name enclosing_lambda expr in
                                      let rest = List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_reads name enclosing_lambda cur_exp)) [] expr_lst in
                                      first@rest
       | ScmApplicTP'(expr,expr_lst) -> let first = find_reads name enclosing_lambda expr in
                                        let rest = List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_reads name enclosing_lambda cur_exp)) [] expr_lst in
                                        first@rest
       | _ -> []
 
       and find_writes name enclosing_lambda body = match body with
       | ScmIf'(test,dit,dif) -> let test1 = find_writes name enclosing_lambda test in
                                 let dit1 = find_writes name enclosing_lambda dit in
                                 let dif1 = find_writes name enclosing_lambda dif in
                                 let lst = test1@dit1 in let lst = lst@dif1 in
                                 lst
       | ScmSeq'(expr_lst) -> List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_writes name enclosing_lambda cur_exp)) [] expr_lst
       | ScmSet'(var,expr) -> let var_type = match var with 
                               | VarFree(_) -> find_writes name enclosing_lambda expr
                               | VarParam(var,_) -> if var=name then [enclosing_lambda] else find_writes name enclosing_lambda expr
                               | VarBound(var,_,_) -> if var=name then [enclosing_lambda] else find_writes name enclosing_lambda expr
                               in var_type  
       | ScmDef'(var,expr) -> find_writes name enclosing_lambda expr 
       | ScmOr'(expr_lst) -> List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_writes name enclosing_lambda cur_exp)) [] expr_lst
       | ScmLambdaSimple'(params,body_expr) -> let is_shadow = List.mem name params in
                                             if is_shadow then []
                                             else let output = match (find_writes name body body_expr) with
                                                               | [] -> []
                                                               | _ -> [body] in output
       | ScmLambdaOpt'(params_lst,last_param,body_expr) -> let params = params_lst@[last_param] in
                                                           let is_shadow = List.mem name params in
                                                           if is_shadow then []
                                                           else let output = match (find_writes name body body_expr) with
                                                               | [] -> []
                                                               | _ -> [body] in output
       | ScmApplic'(expr,expr_lst) -> let first = find_writes name enclosing_lambda expr in
                                      let rest = List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_writes name enclosing_lambda cur_exp)) [] expr_lst in
                                      first@rest
       | ScmApplicTP'(expr,expr_lst) -> let first = find_writes name enclosing_lambda expr in
                                        let rest = List.fold_left (fun cur_lst cur_exp -> cur_lst@(find_writes name enclosing_lambda cur_exp)) [] expr_lst in
                                        first@rest
       | _ -> []
       
 
     and cartesian_product lst1 lst2 = List.concat (List.map (fun i -> List.map (fun j -> (i,j)) lst1) lst2)
 
     and remove_lambda_from_list lambda lst =
         let rec helper l acc = match l with
           | [] -> List.rev acc
           | x::xs when (x=lambda) -> helper xs acc
           | x::xs -> helper xs (x::acc)
         in helper lst []
 
     and remove_duplicates lst =
         let rec helper l acc = match l with
           | [] -> List.rev acc
           | x :: xs -> helper (remove_lambda_from_list x xs) (x::acc)
         in helper lst []
   
   and should_box enclosing_lambda body name = 
     let reads = find_reads name enclosing_lambda body in
     let reads = remove_duplicates reads in
     let writes = find_writes name enclosing_lambda body in
     let writes = remove_duplicates writes in
     let combined_read_write_lst = cartesian_product reads writes in
     let combined_read_write_lst = List.filter (fun (x,y) -> not (x=y)) combined_read_write_lst in
     let output = match combined_read_write_lst with
       | [] -> false
       | _ -> true
       in output
 
     and set_box boxed_env expr = match expr with
       | ScmConst'(sexpr) -> expr
       | ScmVar'(var) -> let var_type = match var with
                           | VarFree(_) -> expr
                           | VarParam(var_name,_) -> let is_boxed = match (lookup_in_env var_name boxed_env) with
                                                               | None -> expr
                                                               | Some(0,minor) -> ScmBoxGet'(var) 
                                                               | Some(_) -> expr in is_boxed
                           | VarBound(var_name,_,_) -> let is_boxed = match (lookup_in_env var_name boxed_env) with
                                                             | None -> expr
                                                             | Some(_) -> ScmBoxGet'(var) in is_boxed
                           in var_type
       | ScmBox'(_) -> expr 
       | ScmBoxGet'(_) -> expr
       | ScmBoxSet'(var,exp) -> ScmBoxSet'(var,set_box boxed_env exp)
       | ScmIf'(test,dit,dif) -> ScmIf'(set_box boxed_env test,set_box boxed_env dit,set_box boxed_env dif)
       | ScmSeq'(expr_lst) -> ScmSeq'(List.map (set_box boxed_env) expr_lst)
       | ScmSet'(var,exp) -> let var_type = match var with
                               | VarFree(_) -> ScmSet'(var,set_box boxed_env exp)
                               | VarParam(var_name,_) -> let is_boxed = match (lookup_in_env var_name boxed_env) with
                                                                         | None -> ScmSet'(var,set_box boxed_env exp)
                                                                         | Some(_) -> ScmBoxSet'(var,set_box boxed_env exp) in is_boxed
                               | VarBound(var_name,_,_) -> let is_boxed = match (lookup_in_env var_name boxed_env) with
                                                             | None -> ScmSet'(var,set_box boxed_env exp)
                                                             | Some(_) -> ScmBoxSet'(var,set_box boxed_env exp) in is_boxed
                               in var_type
       | ScmDef'(var,expr) -> ScmDef'(var,set_box boxed_env expr)
       | ScmOr'(expr_lst) -> ScmOr'(List.map (set_box boxed_env) expr_lst)
       | ScmLambdaSimple'(params,body) -> let boxed_params = List.map (fun x -> (x,should_box expr body x)) params in
                                          let boxed_params = List.mapi (fun idx x -> (idx,x)) boxed_params in
                                          let boxed_params = List.filter (fun (_,(_,should_box)) -> should_box) boxed_params in
                                          let args = List.map (fun (minor,(var_name,_)) -> var_name) boxed_params in
                                          let boxed_params = List.map (fun (minor,(var_name,_)) -> ScmSet'(VarParam(var_name,minor), ScmBox'(VarParam(var_name,minor)))) boxed_params in
                                          let body = set_box (args::boxed_env) body in
                                          let appended_body = match body with
                                                             | ScmSeq'(expr_lst) -> ScmSeq'(boxed_params@expr_lst)
                                                             | _ -> let output = match boxed_params with 
                                                                                   | [] -> body
                                                                                   | _ -> ScmSeq'(boxed_params@[body]) in output
                                          in ScmLambdaSimple' (params,appended_body)
       | ScmLambdaOpt'(first_params,last_param,body) -> let params = first_params@[last_param] in
                                                        let boxed_params = List.map (fun x -> (x,should_box expr body x)) params in
                                                        let boxed_params = List.mapi (fun idx x -> (idx,x)) boxed_params in
                                                        let boxed_params = List.filter (fun (_,(_,should_box)) -> should_box) boxed_params in
                                                        let args = List.map (fun (minor,(var_name,_)) -> var_name) boxed_params in
                                                        let boxed_params = List.map (fun (minor,(var_name,_)) -> ScmSet'(VarParam(var_name,minor), ScmBox'(VarParam(var_name,minor)))) boxed_params in
                                                        let body = set_box (args::boxed_env) body in
                                                        let appended_body = match body with
                                                             | ScmSeq'(expr_lst) -> ScmSeq'(boxed_params@expr_lst)
                                                             | _ -> let output = match boxed_params with 
                                                                                   | [] -> body
                                                                                   | _ -> ScmSeq'(boxed_params@[body]) in output
                                                        in ScmLambdaOpt' (first_params,last_param,appended_body)
       | ScmApplic'(expr,expr_lst) -> ScmApplic'(set_box boxed_env expr,List.map (set_box boxed_env) expr_lst)
       | ScmApplicTP'(expr,expr_lst) -> ScmApplicTP'(set_box boxed_env expr,List.map (set_box boxed_env) expr_lst)
   in set_box [] expr;;
 
   let run_semantics expr =
     box_set
     (*support tail call at the end  *)
       (annotate_tail_calls
          (annotate_lexical_addresses expr))
 
 end;; (* end of module Semantic_Analysis *)