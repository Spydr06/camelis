type stream = {
    mutable line_num : int;
    mutable chr : char list;
    chan : in_channel;
}

let read_char stm =
    match stm.chr with
    | [] -> let c = input_char stm.chan in
        if c = '\n' 
        then let _ = stm.line_num <- stm.line_num + 1 in c
        else c
    | c :: rest -> let _ = stm.chr <- rest in c

let unread_char stm c = stm.chr <- c :: stm.chr
let is_white c = c = ' ' || c = '\t' || c = '\n'

let string_of_char c = String.make 1 c

let rec eat_whitespace stm =
    let c = read_char stm in
        if is_white c then eat_whitespace stm else unread_char stm c

exception Unreachable
exception SyntaxError of string
exception TypeError of string
exception NotFound of string

type lobject = 
    | Fixnum of int
    | Boolean of bool
    | Symbol of string
    | Nil
    | Pair of lobject * lobject
    | Primitive of string * (lobject list -> lobject)

and value = lobject
and name = string

let rec is_list e =
    match e with
    | Nil -> true
    | Pair(a, b) -> is_list b
    | _ -> false

let rec pair_to_list pr =
    match pr with
    | Nil -> []
    | Pair(a, b) -> a::(pair_to_list b)
    | _ -> raise Unreachable

let rec read_sexp stm =
    let is_digit c =
        let code = Char.code c in
            code >= Char.code '0' && code <= Char.code '9'
    in
    let rec read_fixnum acc =
        let nc = read_char stm in
            if is_digit nc 
            then read_fixnum (acc ^ Char.escaped nc)
            else let _ = unread_char stm nc in
                Fixnum (int_of_string acc)
    in
    let is_symstartchar =
        let isalpha = function | 'A'..'Z' | 'a'..'z' -> true
                               | _ -> false
        in
        function | '*'| '/' | '>' | '<' | '=' | '?' | '!' | '-' | '+' -> true
                 | c -> isalpha c
    in
    let rec read_symbol () =
        let is_delimeter = function | '(' | ')' | '{' | '}' | ';' | '"' -> true
                                    | c -> is_white c
        in
        let nc = read_char stm in
        if is_delimeter nc
            then let _ = unread_char stm nc in ""
            else string_of_char nc ^ read_symbol ()
    in
    let rec read_list stm =
        eat_whitespace stm;
        let c = read_char stm in
        if c = ')'
        then Nil
        else
            let _ = unread_char stm c in
            let car = read_sexp stm in
            let cdr = read_list stm in
            Pair(car, cdr)
    in
    eat_whitespace stm;
    let c = read_char stm in
        if is_symstartchar c
        then Symbol(string_of_char c ^ read_symbol ())
        else if c = '(' then read_list stm
        else if (is_digit c) || (c = '~') then read_fixnum (Char.escaped (if c = '~' then '-' else c))
        else if c == '#' then
            match (read_char stm) with
            | 't' -> Boolean(true)
            | 'f' -> Boolean(false)
            | x -> raise (SyntaxError ("Invalid boolean literal `#" ^ (Char.escaped x) ^ "`"))
        else raise (SyntaxError ("Unexpected char `" ^ Char.escaped c ^ "`"))

let rec lookup (n, e) =
    match e with
    | Nil -> raise (NotFound n)
    | Pair(Pair(Symbol n', v), rst) -> if n = n' then v else lookup (n, rst)
    | _ -> raise Unreachable

let rec bind (n, v, e) = Pair(Pair(Symbol n, v), e)

let rec eval_sexp sexp env =
    let eval_if cond iftrue iffalse =
        let (condval, _) = eval_sexp cond env in
        match condval with
        | Boolean(true) -> iftrue
        | Boolean(false) -> iffalse
        | _ -> raise (TypeError "(if bool e1 e2)")
    in
    match sexp with
    | Fixnum(v) -> (Fixnum(v), env)
    | Boolean(v) -> (Boolean(v), env)
    | Symbol(name) -> (lookup (name, env), env)
    | Nil -> (Nil, env)
    | Primitive(n, f) -> (Primitive(n, f), env)
    | Pair(_, _) when is_list sexp -> (
        match pair_to_list sexp with
        | [Symbol "if"; cond; iftrue; iffalse] -> 
            let (ifval, _) = eval_sexp (eval_if cond iftrue iffalse) env in (ifval, env)
        | [Symbol "env"] -> (env, env)
        | [Symbol "val"; Symbol name; exp] ->
            let (expval, _) = eval_sexp exp env in
            let env' = bind (name, expval, env) in
            (expval, env')
        | (Symbol fn)::args -> 
            (match eval_sexp (Symbol fn) env with
            | (Primitive(n, f), _) -> (f args, env)
            | _ -> raise (TypeError "(apply func args)"))
        | _ -> (sexp, env)
    )
    | _ -> (sexp, env)

let rec print_sexp e =
    match e with
    | Fixnum(v) -> print_int v
    | Boolean(b) -> print_string (if b then "#t" else "#f")
    | Symbol(s) -> print_string s
    | Primitive(name, _) -> print_string ("#<primitive:" ^ name ^ ">")
    | Nil -> print_string "nil"
    | Pair(a, b) ->
        let rec print_list l =
            match l with
            | Pair(a, Nil) -> print_sexp a;
            | Pair(a, b) -> print_sexp a; print_string " "; print_list b;
            | _ -> raise Unreachable
        in
        let print_pair p =
            match p with
            | Pair(a, b) -> print_sexp a; print_string " . "; print_sexp b;
            | _ -> raise Unreachable
        in
        print_string "(";
        if is_list e then print_list e else print_pair e;
        print_string ")"

let basis =
    let prim_plus = function
        | [Fixnum(a); Fixnum(b)] -> Fixnum(a + b)
        | _ -> raise (TypeError "(+ int int)")
    in
    let prim_pair = function
        | [a; b] -> Pair(a, b)
        | _ -> raise (TypeError "(pair a b)")
    in
    let newprim acc (name, func) =
        bind (name, Primitive(name, func), acc)
    in
    List.fold_left newprim Nil [
        ("+", prim_plus);
        ("pair", prim_pair);
    ]

let rec repl stm env = 
    print_string "> ";
    flush stdout;
    let sexp = read_sexp stm in
    let (result, env') = eval_sexp sexp env in
        print_sexp result;
        print_newline ();
        repl stm env'

let main =
    let stm = { chr = []; line_num = 1; chan = stdin } in
        repl stm basis