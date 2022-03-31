#use "reader.ml";;
(* Tom Vladi*)
type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> scm_append (ScmPair(scm_list,ScmNil)) sexpr

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> sexpr::(scm_list_to_list ScmNil);;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec dup_exist = function
  | [] -> false
  | hd::tl -> List.exists ((=) hd) tl || dup_exist tl

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(*Constants*)
| ScmVoid -> ScmConst(sexpr)
| ScmNil -> ScmConst(sexpr)
| ScmBoolean(_) -> ScmConst(sexpr)
| ScmChar(_) -> ScmConst(sexpr)
| ScmNumber(_) -> ScmConst(sexpr)
| ScmString(_) -> ScmConst(sexpr)
| ScmVector(_) -> ScmConst(sexpr)
| ScmPair(ScmSymbol "quote",ScmPair(car,ScmNil)) -> ScmConst(car)
| ScmPair(ScmSymbol "quote",simple_cdr) -> ScmConst(simple_cdr)


(*If expr*)
| ScmPair(ScmSymbol "if",
                        ScmPair(test,
                          ScmPair(dit,ScmNil))) -> let test_expr = tag_parse_expression test in
                                                   let dit_expr = tag_parse_expression dit in
                                                   let dif_expr = ScmConst(ScmVoid) in
                                                   ScmIf(test_expr,dit_expr,dif_expr)
| ScmPair(ScmSymbol "if",
                        ScmPair(test,
                            ScmPair(dit,
                              ScmPair(dif,ScmNil)))) -> let test_expr = tag_parse_expression test in
                                                        let dit_expr = tag_parse_expression dit in
                                                        let dif_expr = tag_parse_expression dif in
                                                        ScmIf(test_expr,dit_expr,dif_expr)
(*Lambda expr*)
| ScmPair(ScmSymbol "lambda",
                            ScmPair(vars,body)) -> parse_lambda vars body

(*Set expr*)
| ScmPair(ScmSymbol "set!",
                            ScmPair(var,ScmPair(value,ScmNil))) -> let arg_str = match (tag_parse_expression var) with 
                                                                        | ScmVar(arg) -> arg
                                                                        | _ -> raise (X_syntax_error(sexpr,"Expected variable on LHS of set!")) in
                                                                   parse_set arg_str value
(*Begin expr*)
| ScmPair(ScmSymbol "begin",exprs) -> let x = match exprs with
                                              | ScmPair(sexpr,ScmNil) -> tag_parse_expression sexpr
                                              | ScmPair(sexpr,sexprs) -> 
                                                let first_expr = tag_parse_expression sexpr in
                                                let rest_exprs_lst = List.map tag_parse_expression (scm_list_to_list sexprs) in 
                                                ScmSeq([first_expr]@rest_exprs_lst)
                                              | _ -> raise (X_syntax_error(sexpr,"begin mustn't have empty body")) in x

(* variables *)
| ScmSymbol sym -> if List.mem sym reserved_word_list then raise (X_reserved_word(string_of_sexpr sexpr)) else ScmVar sym 
(* or *) 
| ScmPair (ScmSymbol "or", ScmNil) -> ScmConst(ScmBoolean(false))
| ScmPair (ScmSymbol "or", ScmPair (exp, ScmNil)) -> tag_parse_expression exp
| ScmPair (ScmSymbol "or", exprs) -> let or_exprs = (get_parsed_vars (scm_list_to_list exprs)) in ScmOr(or_exprs)
(* define *)
| ScmPair
   (ScmSymbol "define",
    ScmPair (ScmSymbol (var) as vr, ScmPair (value , ScmNil))) -> 
    if (List.mem var reserved_word_list = false) then  ScmDef (tag_parse_expression vr, tag_parse_expression value) 
    else raise (X_syntax_error (sexpr, "Expected variable on LHS of define"))

(*Application *)
| ScmPair(func, args) -> let parsed_args = (get_parsed_vars (scm_list_to_list args)) in ScmApplic(tag_parse_expression func , parsed_args)


and get_parsed_vars list = 
let parsed_vars = List.map tag_parse_expression list in
parsed_vars

and parse_lambda vars body =
    if scm_is_list vars 
        then
          let vars_lst = make_vars_list vars [] in
          let is_duplicate = dup_exist vars_lst in
          let body_expr = match body with
                            | ScmPair(expr,ScmNil) -> tag_parse_expression expr
                            | ScmPair(car,cdr) -> ScmSeq(List.map tag_parse_expression (scm_list_to_list body))
                            | _ -> raise (X_syntax_error (body,"Body can't be empty")) in
          if is_duplicate then raise (X_syntax_error(vars,"Duplicate vars")) else ScmLambdaSimple(vars_lst,body_expr)
    else
      let vars_lst = make_vars_list_improper vars [] in
      let is_duplicate = dup_exist vars_lst in
      let last_var = get_last_element_improper vars in
      let body_expr = match body with
                      | ScmPair(expr,ScmNil) -> tag_parse_expression expr
                      | ScmPair(car,cdr) -> ScmSeq(List.map tag_parse_expression (scm_list_to_list body))
                      | _ -> raise (X_syntax_error (body,"Body can't be empty")) in
      if is_duplicate then raise (X_syntax_error(vars,"Duplicate vars")) else ScmLambdaOpt(vars_lst,last_var,body_expr)

and parse_set arg_str value = match value with
  | ScmNil -> raise (X_syntax_error (value,"Body can't be empty"))
  | _ -> ScmSet(ScmVar(arg_str),(tag_parse_expression value))
  

and macro_expand sexpr =
match sexpr with
(*and*)
| ScmPair (ScmSymbol "and", ScmNil) -> ScmBoolean(true)
| ScmPair (ScmSymbol "and", ScmPair (expr, ScmNil)) -> expr
| ScmPair(ScmSymbol "and",ScmPair(expr,exprs)) ->ScmPair (ScmSymbol "if",ScmPair (expr,ScmPair (ScmPair(ScmSymbol "and",exprs),ScmPair (ScmBoolean(false), ScmNil))))

(*MIT define expr*)
| ScmPair(ScmSymbol "define",
  ScmPair(
    ScmPair(var,args),body)) -> expand_mit_def var args body 

(*let expr*)
| ScmPair(ScmSymbol "let",
                        ScmPair(bindings,body)) -> expand_let bindings body
(*let* expr*)
| ScmPair(ScmSymbol "let*",
                        ScmPair(ScmNil,cdr)) -> macro_expand (ScmPair(ScmSymbol "let",ScmPair(ScmNil,cdr)))
| ScmPair(ScmSymbol "let*",
                        ScmPair(
                          ScmPair(
                          ScmPair(arg,ScmPair(exp,ScmNil)),ScmNil),cdr)) -> macro_expand (ScmPair(ScmSymbol "let",ScmPair(ScmPair(ScmPair(arg,ScmPair(exp,ScmNil)),ScmNil),cdr)))
| ScmPair(ScmSymbol "let*",
                        ScmPair(bindings,body)) -> expand_let_star bindings body

(*let-rec expr*)
| ScmPair(ScmSymbol "letrec",
                        ScmPair(ScmNil,cdr)) -> macro_expand (ScmPair(ScmSymbol "let",ScmPair(ScmNil,cdr)))
| ScmPair(ScmSymbol "letrec",
                        ScmPair(bindings,body)) -> expand_letrec bindings body

(*Quasiquote*)
| ScmPair(ScmSymbol "quasiquote",ScmPair(y,ScmNil)) -> quasiquote_basic_expand y

(*Cond expr*)
| ScmPair(ScmSymbol "cond",
        ribs) -> let x = match (scm_list_length sexpr) with
        | 2 -> expand_cond ribs ScmNil
        | _ -> expand_cond_general sexpr in x
| _ -> sexpr

and expand_cond_general sexpr = match sexpr with
| ScmPair(ScmSymbol "cond",
        ScmPair(ScmPair(rib,ribs),ScmNil)) -> expand_cond rib ribs
| ScmPair(ScmSymbol "cond",
        ScmPair(rib,ribs)) -> expand_cond rib ribs
| _ -> sexpr

and make_args_lst_from_bindings bindings =
  let bindings_lst = scm_list_to_list bindings in
  let rec bindings_args_lst lst cur_lst = match lst with
    | ScmPair(x,y)::tail -> bindings_args_lst tail (cur_lst@[x])
    | [] -> cur_lst
    | _ -> raise (X_syntax_error(bindings,"let problem")) in
    list_to_proper_list (bindings_args_lst bindings_lst [])

and make_bindings_vals_lst_from_bindings bindings =
  let bindings_lst = scm_list_to_list bindings in
  let rec bindings_vals_lst lst cur_lst = match lst with
    | ScmPair(x,ScmPair(y,ScmNil))::tail -> bindings_vals_lst tail (cur_lst@[y])
    | ScmPair(x,y)::tail -> bindings_vals_lst tail (cur_lst@[y])
    | [] -> cur_lst 
    | _ -> raise (X_syntax_error(bindings,"let problem")) in
    list_to_proper_list (bindings_vals_lst bindings_lst [])
    

and make_vars_list vars cur_lst =
  match vars with
  | ScmNil -> cur_lst
  | ScmPair(ScmSymbol(var),cdr) -> if List.mem var reserved_word_list then raise (X_reserved_word("Can't use arg as reserved word"))
                                                                      else make_vars_list cdr (cur_lst@[var])
  | _ -> raise (X_syntax_error(vars,"Args must be symbols1"))

and make_vars_list_improper vars cur_lst = 
  match vars with
  | ScmPair(ScmSymbol(x),ScmSymbol(y)) -> if List.mem x reserved_word_list then raise (X_reserved_word("Can't use arg as reserved word")) 
                                                                      else cur_lst@[x]
  | ScmPair(ScmSymbol(var),cdr) -> if List.mem var reserved_word_list then raise (X_reserved_word("Can't use arg as reserved word")) 
                                                                      else make_vars_list_improper cdr (cur_lst@[var])
  | ScmSymbol(x) -> if List.mem x reserved_word_list then raise (X_reserved_word("Can't use arg as reserved word")) 
                                                                      else cur_lst
  | _ -> raise (X_syntax_error(vars,"Args must be symbols2"))

and get_last_element_improper vars = 
  match vars with
  | ScmSymbol(x) -> if List.mem x reserved_word_list then raise (X_reserved_word("Can't use arg as reserved word")) 
                                                                      else x
  | ScmPair(ScmSymbol(x),ScmSymbol(y)) -> if List.mem y reserved_word_list then raise (X_reserved_word("Can't use arg as reserved word")) 
                                                                      else y
  | ScmPair(ScmSymbol(x),cdr) -> get_last_element_improper cdr
  | _ -> raise (X_syntax_error(vars,"Args must be symbols3"))

and expand_mit_def var args body =
  let def_expr = ScmPair(ScmSymbol "define",ScmNil) in
  let def_expr = scm_append def_expr (ScmPair(var,ScmNil)) in
  let lambda_expr = ScmPair(ScmSymbol "lambda", ScmNil) in
  let lambda_expr = scm_append lambda_expr (ScmPair(args,ScmNil)) in
  let lambda_expr = scm_append lambda_expr body in
  let def_expr = scm_append def_expr (ScmPair(lambda_expr,ScmNil)) in
  def_expr

and expand_let bindings body =
  let args_lst = make_args_lst_from_bindings bindings in
  let bindings_vals = make_bindings_vals_lst_from_bindings bindings in
                        ScmPair(
                          ScmPair(ScmSymbol "lambda",ScmPair(args_lst,body))
                          ,bindings_vals)

and expand_let_star bindings body =
  let first_var = match bindings with
    | ScmPair(ScmPair(x,y),cdr) -> x
    | _ -> raise (X_syntax_error (bindings,"Problem with let*")) in
  let first_val = match bindings with
    | ScmPair(ScmPair(x,y),cdr) -> y
    | _ -> raise (X_syntax_error (bindings,"Problem with let*")) in
  let rest_let = match bindings with
    | ScmPair(ScmPair(x,y),cdr) -> cdr 
    | _ -> raise (X_syntax_error (bindings,"Problem with let*")) in
  let to_expand = ScmPair(ScmSymbol "let*",
  ScmPair(rest_let,body)) in
  let to_expand = macro_expand to_expand in
  let to_expand =
  ScmPair(ScmSymbol "let",
  ScmPair(
  ScmPair(ScmPair(first_var,first_val),ScmNil),ScmPair(to_expand,ScmNil))) in
  macro_expand to_expand

and expand_letrec bindings body =
  let args_lst = scm_map (fun x -> match x with 
    | ScmPair(arg,_val) -> arg
    | _ -> raise (X_syntax_error(bindings,"bindings should be pairs"))
  ) bindings  in
  let bindings_vals = scm_map (fun x -> match x with
    | ScmPair(arg,ScmPair(_val,ScmNil)) -> _val
    | ScmPair(arg,_val) -> _val
    | _ -> raise (X_syntax_error(bindings,"bindings should be pairs"))
  ) bindings in
  let zipped_bindings_whatever = scm_zip (fun sexpr1 sexpr2 -> ScmPair(sexpr1,ScmPair(ScmPair (ScmSymbol "quote", ScmPair (ScmSymbol "whatever", ScmNil)),ScmNil))) 
                                                args_lst bindings_vals in
  let set_bindings = scm_zip (fun sexpr1 sexpr2 -> ScmPair(ScmSymbol "set!",ScmPair(sexpr1,ScmPair(sexpr2,ScmNil)))) 
                                args_lst bindings_vals in
  let final_let = ScmPair(ScmSymbol "let",
  ScmPair(zipped_bindings_whatever,
  ScmNil
  )) in
  let final_let = scm_append final_let set_bindings in
  let final_let = scm_append final_let body in
  let final_let = macro_expand final_let in
  final_let

and expand_cond rib ribs =
 let rib = match (scm_list_length rib) with
 | 1 -> let x =match rib with | ScmPair(car,ScmNil) -> car
                               | _ -> rib in x
 | _ -> rib in
 let x =match rib with
  | ScmPair(ScmSymbol "else",body) -> expand_else_rib body
  | ScmPair(test,ScmPair(ScmSymbol "=>",body)) -> expand_arrow_rib test body ribs
  | ScmPair(test,body) -> expand_reg_rib test body ribs
  | ScmNil -> ScmVoid
  | _ -> raise (X_syntax_error(rib,"cond rib error")) in x

and expand_reg_rib test body ribs =
  let if_stmt = ScmPair(ScmSymbol "if",ScmNil) in
  let if_stmt = scm_append if_stmt (ScmPair (test,ScmNil)) in
  let begin_stmt = ScmPair(ScmSymbol "begin",ScmNil) in
  let single_body = scm_list_length body in
  let begin_stmt = match single_body with
  | 1 -> (macro_expand body)
  | _ -> scm_append begin_stmt (macro_expand body) in
  let rest = match ribs with 
      | ScmPair(car,cdr) -> expand_cond car cdr 
      | ScmNil -> ScmNil
      | _ -> raise (X_syntax_error(ribs,"cond rib error")) in
  let if_stmt = match single_body with
  | 1 -> scm_append if_stmt begin_stmt 
  | _ -> scm_append if_stmt (ScmPair(begin_stmt,ScmNil)) in
  let if_stmt = match rest with
          | ScmNil -> if_stmt
          | _ -> scm_append if_stmt (ScmPair(rest,ScmNil)) in
  if_stmt

and expand_arrow_rib test body ribs =
  let _let_stmt = ScmPair(ScmSymbol "let",ScmNil) in
  let test_rib = ScmPair(ScmSymbol "value",ScmPair(test,ScmNil)) in
  let f_rib = ScmPair(ScmSymbol "f",ScmNil) in
  let lambda_stmt = ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,body)) in
  let f_rib = scm_append f_rib (ScmPair(lambda_stmt,ScmNil)) in
  let rest = match ribs with 
      | ScmPair(car,cdr) -> expand_cond car cdr 
      | ScmNil -> ScmNil
      | _ -> raise (X_syntax_error(ribs,"cond rib error")) in
  let rest_rib = ScmPair(ScmSymbol "rest",ScmNil) in
  let lambda_rest = ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,ScmPair(rest,ScmNil))) in
  let rest_rib = scm_append rest_rib (ScmPair(lambda_rest,ScmNil)) in
  let final_if = ScmPair(ScmSymbol "if",ScmPair(ScmSymbol "value",ScmNil)) in
  let final_if = scm_append final_if (ScmPair(
      ScmPair(ScmPair(ScmSymbol "f",ScmNil),ScmPair(ScmSymbol "value",ScmNil)),ScmNil)
  ) in
  let final_if = scm_append final_if (ScmPair(ScmPair(ScmSymbol "rest",ScmNil),ScmNil)) in
  let ribs = scm_append (ScmPair(test_rib,ScmNil)) (ScmPair(f_rib,ScmNil)) in
  let ribs = scm_append ribs (ScmPair(rest_rib,ScmNil)) in
  let _let_stmt = scm_append _let_stmt (ScmPair(ribs,ScmNil)) in
  let _let_stmt = scm_append _let_stmt (ScmPair(final_if,ScmNil)) in
  macro_expand _let_stmt 

and expand_else_rib body =
  let begin_stmt = ScmPair(ScmSymbol "begin",ScmNil) in
  let single_body = scm_list_length body in
  let begin_stmt = match single_body with
  | 1 -> let opened_body = match body with | ScmPair(car,cdr) -> car | _ -> body in opened_body
  | _ -> scm_append begin_stmt body in
  begin_stmt
  
  


and quasiquote_basic_expand y = match y with
                                            | ScmPair(ScmSymbol "unquote",ScmPair(cadr,ScmNil)) -> cadr
                                            | ScmPair(ScmSymbol "unquote-splicing",ScmPair(cadr,ScmNil)) -> ScmPair(ScmSymbol "quote",ScmPair(ScmPair(ScmSymbol "unquote-splicing",ScmPair(cadr,ScmNil)),ScmNil))
                                            | ScmSymbol(_) -> ScmPair(ScmSymbol "quote",ScmPair(y,ScmNil))
                                            | ScmNil -> ScmPair(ScmSymbol "quote",ScmPair(ScmNil,ScmNil))
                                            | ScmVector(sexpr_list) -> let vector_app = ScmPair(ScmSymbol "list->vector",ScmNil) in
                                                                       let scm_lst = list_to_proper_list sexpr_list in
                                                                       let scm_lst = quasiquote_basic_expand scm_lst in
                                                                       let vector_app = scm_append vector_app (ScmPair(scm_lst,ScmNil)) in
                                                                       vector_app
                                            | ScmPair(car,cdr) -> let expanded = match car with
                                                                  | ScmPair(ScmSymbol "unquote-splicing", ScmPair(cadr,ScmNil)) -> 
                                                                          let appended = ScmPair(ScmSymbol "append",ScmNil) in
                                                                          let appended = scm_append appended (ScmPair(cadr,ScmNil)) in
                                                                          let appended = scm_append appended (ScmPair((quasiquote_basic_expand cdr),ScmNil)) in
                                                                          appended
                                                                  | _ -> let appended = ScmPair(ScmSymbol "cons",ScmNil) in
                                                                         let appended = scm_append appended (ScmPair((quasiquote_basic_expand car),ScmNil)) in
                                                                         let appended = scm_append appended (ScmPair((quasiquote_basic_expand cdr),ScmNil)) in
                                                                         appended in
                                                                         expanded
                                            | _ -> y
end;; 

