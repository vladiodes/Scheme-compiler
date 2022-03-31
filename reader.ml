(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 (* Vladi and Tom*)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_line_comment str = 
  let nt_end = disj (unitify (char '\n')) (unitify nt_end_of_input) in
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end) in
  let nt1 = unitify nt1 in
  nt1 str
and nt_paired_comment str = 
  let nt_open = char '{' in
  let nt_close = char '}' in
  let nt_x = diff nt_any (disj nt_open nt_close) in
  let nt_inside = disj_list [unitify nt_string; unitify nt_char;unitify nt_comment;unitify nt_x] in
  let nt_inside = star nt_inside in
  let nt1 = caten_list [unitify nt_open; unitify nt_inside; unitify nt_close] in
  let nt1 = unitify nt1 in
  nt1 str

and nt_sexpr_comment str = 
  let n1_prefix = word "#;" in
  let nt1 = caten n1_prefix (maybe nt_sexpr) in
  let nt1 = unitify nt1 in
  nt1 str

and nt_comment str = 
  disj_list
    [nt_paired_comment;
     nt_sexpr_comment;
     nt_line_comment] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1

and nt_int str = 
  let _digit_ = range '0' '9' in
  let _natural_ = plus(_digit_) in
  let _plus_ = char '+' in 
  let _minus_ = char '-' in 
  (* add maybe and pattern matching*)
  let nt1 = caten (disj _plus_ _minus_) _natural_ in
  let nt1 = pack nt1 (fun (a, b)-> let res = int_of_string(list_to_string b) in  if (a='-') then -res else res) in
  let nt2 = pack _natural_ (fun res -> int_of_string(list_to_string res)) in
  let nt1 = disj nt1 nt2 in
  nt1 str
  
and nt_frac str = 
  let slash = char '/' in
  let nt1 = caten (caten nt_int slash) nt_integer_part in
  let nt1 = pack nt1 (fun ((nume, slash), deno) ->  
    let _gcd = gcd nume deno in
    let nume = nume/_gcd in
    let deno = deno/_gcd in 
    if deno == 0 then raise X_no_match 
    else (if deno < 0 then ScmRational (-nume,-deno) else ScmRational(nume,deno))) in
  nt1 str

and nt_integer_part str = 
  let _digits_ = plus(range '0' '9') in
  let nt1 = pack _digits_ (fun num -> int_of_string (list_to_string num)) in
  nt1 str
  
and nt_float str = 
  let nt_sign = disj (char '-') (char '+') in
  let nt_sign = maybe nt_sign in
  let nt1 = disj_list [nt_floatA;nt_floatB;nt_floatC] in
  let nt1 = caten nt_sign nt1 in
  let nt1 = pack nt1 (fun (sign,a)-> match sign with 
  | None -> ScmReal (float_of_string a)
  | Some ch -> match ch with 
                | '-' -> ScmReal (-.float_of_string a)
                | _ -> ScmReal (float_of_string a)
  ) in
  nt1 str

(*All floatX return a string that represents a number in ocaml*)
and nt_floatA str =
  let nt_int_part = plus (range '0' '9') in
  let nt_dot = char '.' in
  let nt1 = caten (caten nt_int_part nt_dot) (caten (maybe nt_int_part) (maybe nt_exponent)) in
  let nt1 = pack nt1 (fun ((int_part,_),(mantissa,exponent)) -> match (mantissa,exponent) with
                                            |(None,None) -> (list_to_string int_part)^"."
                                            |(None,Some exp) -> (list_to_string int_part)^"."^exp
                                            |(Some mant,None) -> (list_to_string int_part)^"."^(list_to_string mant)
                                            |(Some mant, Some exp) -> (list_to_string int_part)^"."^(list_to_string mant)^exp) in
  nt1 str

and nt_floatB str =
  let nt_int_part = plus (range '0' '9') in
  let nt_dot = char '.' in
  let nt1 = caten nt_dot (caten nt_int_part (maybe nt_exponent)) in
  let nt1 = pack nt1 (fun (_,(mantissa,exponent)) -> match exponent with
                                            |None -> "."^(list_to_string mantissa)
                                            |Some exp -> "."^(list_to_string mantissa)^exp) in
  nt1 str

and nt_floatC str =
  let nt_int_part = plus (range '0' '9') in
  let nt1 = caten nt_int_part nt_exponent in
  let nt1 = pack nt1 (fun (int_part,exp) -> (list_to_string int_part)^exp) in
  nt1 str



and nt_exponent str = 
  let nt_token = disj_list[word "e"; word "E"; word "*10^"; word "*10**"] in
  let nt_token = caten nt_token nt_int in
  let nt_token = pack nt_token (fun (_,num) -> "e"^(string_of_int num)) in
  nt_token str

 
 
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt2 = word_ci "#t" in
  let nt1 = pack nt1 (fun _ -> ScmBoolean false) in
  let nt2 = pack nt2 (fun _ -> ScmBoolean true) in
  let nt3 = disj nt1 nt2 in
  nt3 str
and nt_char_simple str = 
  let nt0 = range (char_of_int 32) (char_of_int 127) in
  nt0 str
and make_named_char char_name ch =
  let nt0 = word_ci char_name in
  let nt1 = pack nt0 (function _ -> ch) in
  nt1 
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "nul" (char_of_int 0));
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str = 
  let nt1 = char_ci 'x' in
  let nt2 = range '0' '9' in
  let nt3 = range_ci 'a' 'f' in
  let nt3 = disj nt2 nt3 in
  let nt3 = plus nt3 in
  let nt3 = caten nt1 nt3 in
  let nt3 = pack nt3 (function (_,y) -> match List.length y with
  | 1 -> char_of_int (int_of_string (String.make 1 '0' ^ String.make 1 'x' ^ (list_to_string y)))
  | 2 -> char_of_int (int_of_string (String.make 1 '0' ^ String.make 1 'x' ^ (list_to_string y)))
  | _ -> raise X_no_match)  in
  nt3 str

and nt_char str = 
  let nt0 = word "#\\" in
  let nt1 = caten nt0 nt_char_simple in
  let nt1 = pack nt1 (function (hd,tail) -> ScmChar tail) in
  let nt2 = caten nt0 nt_char_named in
  let nt2 = pack nt2 (function (hd,tail) -> ScmChar tail) in
  let nt4 = caten nt0 nt_char_hex in
  let nt4 = pack nt4 (function (hd,tail) -> 
        ScmChar tail) in
  let nt3 = disj nt2 (disj nt4 nt1) in
  let nt3 = not_followed_by nt3 nt_symbol in
  nt3 str
  
and nt_symbol_char str = 
  let nt1 = range '0' '9' in
  let nt2 = range_ci 'a' 'z' in
  let nt3 = disj_list [
    (char '!');
    (char '$');
    (char '^');
    (char '*');
    (char '-');
    (char '_');
    (char '=');
    (char '+');
    (char '<');
    (char '>');
    (char '?');
    (char '/');
    (char ':')] in
    let nt4 = disj (disj nt1 nt2) nt3 in
    nt4 str
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str

and nt_string str = 
  let nt1 = char '\"' in
  let nt_str_chars = disj_list[nt_string_literal_char;nt_string_hex_char;nt_string_meta_char] in
  let nt_str_chars = pack nt_str_chars (fun ch -> ScmChar ch) in
  let nt_str_chars = disj nt_string_interpolated nt_str_chars in
  let nt_str_chars = star nt_str_chars in
  let nt1 = caten nt1 (caten nt_str_chars nt1) in
  let nt1 = pack nt1 (fun (_,(chars,_)) -> 
        if is_dynamic chars = false then ScmString (list_to_string (List.map 
                                                        (fun (x) -> match x with
                                                        | ScmChar(ch) -> ch
                                                        | _ -> '!') chars)) (* Will never get here*)
        else match List.length chars with
          | 1 -> List.find (fun _ -> true) chars
          | _ -> ScmPair (ScmSymbol "string-append",
                        (List.fold_right (fun sexpr expr -> ScmPair (sexpr,expr)) (create_str_list_with_inter chars "" []) ScmNil))
                 
  ) in
  nt1 str

and is_dynamic lst = match lst with
  | [] -> false
  | ScmChar(_)::t -> is_dynamic t
  | ScmPair(_,_)::t -> true
  | _ -> false (* Will never get here*)


and create_str_list_with_inter lst cur_string cur_lst = match lst with
  | [] -> if cur_string = "" then cur_lst else (cur_lst @ [ScmString cur_string])
  | ScmChar(ch)::t -> create_str_list_with_inter t (cur_string ^ (String.make 1 ch)) cur_lst
  | ScmPair(x,y)::t ->  if cur_string = "" then create_str_list_with_inter t "" (cur_lst @ [(ScmPair(x,y))])
                        else create_str_list_with_inter t "" (cur_lst @ [(ScmString cur_string)] @ [(ScmPair(x,y))])
  | _ -> cur_lst (* Will never get here*)


and nt_string_literal_char str =
  let nt1 = nt_any in
  let nt_not = disj_list [char '\\'; char '"'; char '~'] in
  let nt1 = diff nt1 nt_not in
  nt1 str 

and nt_string_meta_char str =
  let nt1 = pack (word "\\") (fun _ -> '\\') in
  let nt2 = pack (word "\\t") (fun _ -> '\t') in
  let nt3 = pack (word "\\f") (fun _ -> char_of_int 12) in
  let nt4 = pack (word "\\n") (fun _ -> '\n') in
  let nt5 = pack (word "\\r") (fun _ -> '\r') in
  let nt6 = pack (word "~~") (fun _ -> '~') in
  let nt7 = pack (word "\\\"") (fun _ -> '"') in
  let nt1 = disj_list [nt2; nt3; nt4; nt5; nt6;nt7 ;nt1] in
  nt1 str

and nt_string_hex_char str = 
  let nt1 = word "\\" in
  let nt2 = char ';' in
  let nt1 = caten nt1 (caten nt_char_hex nt2) in
  let nt1 = pack nt1 (fun (_,(char,_)) -> char) in
  nt1 str


and nt_string_interpolated str = 
  let nt1 = word "~{" in
  let nt2 = char '}' in
  let nt1 = caten nt1 (caten nt_sexpr nt2) in
  let nt1 = pack nt1 (fun (_,(sexpr,_)) -> 
              ScmPair (ScmSymbol "format", 
                  ScmPair (ScmString "~a", 
                    ScmPair (sexpr,ScmNil)))
  ) in 
  nt1 str

and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str

and nt_list str = 
  let nt1 = disj nt_proper_list nt_improper_list in
  nt1 str

and nt_improper_list str =
  let nt1 = char '(' in
  let nt2 = char ')' in
  let nt_dot = char '.' in
  let nt_lst = caten (caten (caten (nt1) (plus nt_sexpr)) (caten (nt_dot) (nt_sexpr))) (nt2) in
  let nt_lst = pack nt_lst (fun ((((_,exps),(_,last_expr)),_)) ->
                    List.fold_right
                          (fun sexpr expr -> ScmPair (sexpr, expr)) exps last_expr
  ) in
  nt_lst str

and nt_proper_list str =
  let nt1 = char '(' in
  let nt2 = char ')' in
  let nt3 = caten nt_skip_star (char ')') in
  let nt3 = caten nt1 nt3 in
  let nt3 = pack nt3 (fun _ -> ScmNil) in
  let nt_lst = caten nt1 (caten (star nt_sexpr) nt2) in
  let nt_lst = pack nt_lst (fun (_,(exps,_)) -> 
      List.fold_right
                    (fun sexpr expr -> ScmPair (sexpr, expr)) exps ScmNil 
    ) in
  let nt_lst = disj nt3 nt_lst in
  nt_lst str


and make_quote_char quote quote_name =
  let nt0 = word quote in
  let nt1 = pack nt0 (function _ -> ScmSymbol quote_name) in
  nt1 

and nt_quoted_forms str = 
  let nt_quote = disj_list [(make_quote_char "'" "quote");
               (make_quote_char "`" "quasiquote");
               (make_quote_char ",@" "unquote-splicing");
               (make_quote_char "," "unquote")] in
  let nt_quote = caten nt_quote nt_sexpr in
  let nt_quote = pack nt_quote (fun (quote,sexpr) -> ScmPair (quote, 
                                                              ScmPair (sexpr, ScmNil))) in
  nt_quote str
  

and nt_sexpr str = 
  let nt1 = disj_list [nt_number;nt_boolean; nt_symbol; nt_char; nt_quoted_forms; nt_vector; nt_list; nt_string] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;
(*
  let nt1 =
    disj_list [nt_number; ; ; ;
               nt_string; ; nt_list; ] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;
  *)

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
