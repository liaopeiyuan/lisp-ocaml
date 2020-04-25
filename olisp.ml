(* Lisp interpreter via GADT and Subtyping *)
(* Author: Peiyuan Liao (alexander_liao@outlook.com) *)

let debug = false;

(* Either *)
type ('f, 's) e = | L of 'f | R of 's

type symb
type num
type l
type atom = [ `A ]
type exp = [ atom | `B ]
type env

(* ragged higher-dimensional array for AST *)
type 'a ele = Ele of 'a | Li of 'a ele list

type 'a scheme_obj =
    | Symbol : string -> symb scheme_obj
    | Number : (int64,float) e -> num scheme_obj
    | T : num scheme_obj
    | F : num scheme_obj
    | Atom : (symb scheme_obj, num scheme_obj) e -> atom scheme_obj
    | List : atom scheme_obj ele list -> l scheme_obj
    | Exp : (atom scheme_obj, l scheme_obj) e -> exp scheme_obj
    | Epsilon : exp scheme_obj
    | Env : lookup -> env scheme_obj
and store = 
    | Proc of (l scheme_obj -> exp scheme_obj) 
    | Ref of num scheme_obj
    | UserDefProc of (symb scheme_obj list * exp scheme_obj * env scheme_obj)
                      (* parms, body, env *)
                      (* Remark that we can control laziness by eval (or not) the
                        body argument before storing a lambda into UserDefProc *)
and lookup =
    | Innermost of (symb scheme_obj, store) Hashtbl.t
    | Outer of ((symb scheme_obj, store) Hashtbl.t * lookup)

type builtin = Quote | If | Define | Set | Lambda | NotABuiltin

let atom_ele_to_exp (x : atom scheme_obj ele) : exp scheme_obj = match x with Ele x' -> Exp (L (x')) | Li x' ->  Exp (R (List x'))

let quote (x : atom scheme_obj ele list) : exp scheme_obj = match x with 
            |  [] -> failwith "Invalid quote: (quote) []" 
            |  ((Ele e)::_) -> Exp (L e) 
            |  ((Li (es))::_)  -> Exp (R (List es))

let condition (x: exp scheme_obj) (e1: atom scheme_obj ele) (e2: atom scheme_obj ele) :> exp scheme_obj = 
    let condition' x e1 e2 : atom scheme_obj ele =  match x with
            | (Exp (L (Atom (R (F))))) -> e2
            | _ -> e1
    in
    match condition' x e1 e2 with
            | Ele (e') -> Exp (L (e'))
            | Li (e') -> Exp (R (List (e')))

let check_builtin a = match a with
    | (Symbol "quote") -> Quote
    | (Symbol "if") -> If
    | (Symbol "define") -> Define
    | (Symbol "set!") -> Set
    | (Symbol "lambda") -> Lambda
    | _ -> NotABuiltin

let rec tokenize (chars: string) : string list = 
    let split = Str.split (Str.regexp "[ \t]+") in
    let explode s = List.init (String.length s) (String.get s) in
    let replace s = List.fold_left 
                    (fun x y -> let c = Char.escaped y in 
                                match c with 
                                    | "(" -> x^"( " 
                                    | ")" -> x^" )"
                                    |_ -> x^c) "" s 
    in
    chars |> explode |> replace |> split

let atom (token: string) : atom scheme_obj = begin try
    let x = Int64.of_string token in Atom (R (Number (L x)))
    with Failure _ -> 
        begin try 
            let y = Float.of_string token in Atom (R (Number (R y)))
        with Failure _ -> Atom(L (Symbol token) )
        end
    end

let rec print_list (a: string list) b = if not(debug) then () else match a with
   | [] -> (Printf.printf "%s\n" b; ())
   | x::xs -> (Printf.printf "%s " (x) ; print_list xs b)

let rec read_from_tokens (tokens: string list ref) : 'a ele = 
    let () = print_list (!tokens) "list" in
    match !tokens with
   | [] -> failwith "unexptected EOF"
   | "("::xs -> 
        let result = ref [] in
        let () = tokens := xs in
        (
            while (List.hd(!tokens) <> ")") do
                result := ((read_from_tokens(tokens)))::(!result)
            done; 
            tokens := List.tl (!tokens); 
            Li (!result |> List.rev) 
        )
   | ")"::_ -> failwith "unexpected )" 
   | x::xs->  let () = tokens := xs in Ele (atom(x))

let parse (program : string) : exp scheme_obj =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens in
    match result with 
        | Li a -> Exp(R (List (a)) )
        | Ele b -> Exp (L b)
and _parse (program : string) : atom scheme_obj ele list =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens in
    match result with
        | Li a -> a
        | Ele b -> [Ele b] 

let literal x = Exp (L (Atom (R (Number (L x))))) 
let float_literal x = Exp (L (Atom (R (Number (R x))))) 

let basic_environment (_: unit) : env scheme_obj =
    let hs: (symb scheme_obj, store) Hashtbl.t = Hashtbl.create 42 in
    let rec add l = match l with
        | List [] -> literal 0L
        | List (  (Ele (Atom (R (Number (L a)))) )::xs  ) -> (match add(List xs) with
                | Exp (L (Atom (R (Number (L sum))))) ->  literal (Int64.add sum a)
                | Exp (L (Atom (R (Number (R sum))))) ->  float_literal (Int64.to_float(a) +. sum)
                | _ -> failwith "incorrect usage of add")
        | List (  (Ele (Atom (R (Number (R a)))) )::xs  ) -> (match add(List xs) with
                | Exp (L (Atom (R (Number (R sum))))) ->  float_literal (sum +. a)
                | Exp (L (Atom (R (Number (L sum))))) ->  float_literal ( Int64.to_float(sum) +. a)
            | _ -> failwith "incorrect usage of add")
      | _ -> failwith "incorrect usage of add"
    in
    let pi = Ref (Number (R Float.pi)) in
    let listify = Proc (fun x -> Exp (R x)) in
    (   
        Hashtbl.add hs (Symbol "+") (Proc add);
        Hashtbl.add hs (Symbol "pi") pi;
        Hashtbl.add hs (Symbol "list") listify;
        Env (Innermost hs)
    )

let rec find (h: env scheme_obj) (key: symb scheme_obj) = match h with
    | Env (Innermost hs) -> Hashtbl.find hs key
    | Env (Outer (hs, inner)) -> try (find (Env inner) key) with Not_found -> Hashtbl.find hs key

let rec eval (e: exp scheme_obj) (env: env scheme_obj ref) : exp scheme_obj = e
and prune (env: env scheme_obj ref) (x : atom scheme_obj ele) : atom scheme_obj ele =   
    let rec subtl (x': atom scheme_obj ele list) :> atom scheme_obj ele = 
            match (eval (Exp (R (List x'))) env) with  
                | Exp (L x) -> Ele x 
                | Exp (R (List x)) -> (Li x) 
                | _ -> failwith "sub-expressions not correctly evaluated" in
    let rec subte (x': atom scheme_obj) :> atom scheme_obj ele = 
            match (eval (Exp (L x')) env) with 
                | Exp (L x) -> Ele x 
                | Exp (R (List x)) -> (Li x) 
                | _ -> failwith "sub-expressions not correctly evaluated" in 
    (match x with | Ele x' -> (subte x') | Li x' -> (subtl x')) 

(* To Be Implemented
let rec eval (e: exp scheme_obj) (env: env scheme_obj ref) : exp scheme_obj = e
*)

let create_user_env ( (params, args, env) : symb scheme_obj list * store list * lookup) : lookup =
    let rec zip params args hs = match ( params,  args) with 
        | ([], []) -> hs
        | (x::xs, y::ys) -> (Hashtbl.add hs x y; zip xs ys hs)
        | _ -> failwith "inproper user defined procedure"
    in
    let hs = Hashtbl.create 42 in
    let dict = zip params args hs in
    let rec update_env (env, inner) = match env with
       | Innermost hs -> Outer (hs, inner)
       | Outer (hs, outin) -> Outer (hs, update_env(outin, inner))
    in

    update_env (env, Innermost(dict))

let eval_user_proc (p: store) (args: l scheme_obj) : exp scheme_obj =
    let rec to_store_list args = (match args with 
        | List [] -> []
        | List ( (Ele (Atom (R x)))::xs) -> (Ref x) :: (to_store_list (List xs))
        | _ -> failwith "incorrect usage of eval_user_proc")
    in
    match p with
        | UserDefProc (params, body, Env env) -> eval body (ref (Env (create_user_env(params, to_store_list args, env))))
        | _ -> failwith "incorrect usage of eval_user_proc"


let environ = ref (basic_environment ())

let program = "(define (merge L M) (if (null? L) M (if (null? M) L (if (< (car L) (car M)) (cons (car L) (merge (cdr L) M)) (cons (car M) (merge (cdr M) L))))))"
let program = "(list (list 1 2 3) (list (list 4 5) ) 2 3)"

let a = tokenize(program)

let res = parse(program) 


let num_str (n : num scheme_obj) : string = match n with
    | Number (L s) -> Int64.to_string s
    | Number (R s) -> Float.to_string s
    | T -> "#t"
    | F -> "#f"

let rec to_string (obj: exp scheme_obj) : string =     
    (match obj with
    | Epsilon -> ""
    | Exp (L (Atom (L (Symbol s))))-> s
    | Exp (L (Atom (R (n))))-> num_str (n)
    | Exp (R (List l))-> match l with 
        | [] -> "()"
        | (Ele (Atom (L (Symbol s))))::xs -> (match (to_string'(xs)) with "" -> "("^s^")" | str -> "("^s^" "^str^")")
        | (Ele (Atom (R (n))))::xs ->  (match (to_string'(xs)) with "" -> "("^(num_str (n))^")" | str -> "("^(num_str (n))^" "^str^")")
        | (Li (ll))::xs -> let temp = (to_string(Exp (R (List ll)))) in (match to_string'(xs) with ""-> "("^temp^")" | str ->  "("^temp^" "^str^")")
    )
and to_string' (obj) : string = (match obj with
        | [] -> ""
        | (Ele (Atom (L (Symbol s))))::xs -> (match to_string'(xs) with "" -> s | str -> s^" "^str)
        | (Ele (Atom (R (n))))::xs -> (match to_string'(xs) with "" -> (num_str  n) | str -> (num_str  n)^" "^str)
        | (Li (ll))::xs -> let temp = ( to_string(Exp (R (List ll))) ) in (match to_string'(xs) with "" -> temp | str -> temp^" "^str))
    
let read_eval_print_loop (_ : unit) : unit =
  let cond = ref true in 
  let environ = () |> basic_environment |> ref in 
  while !cond do 
    (
        Printf.printf "> ";
        let input = read_line () in 
        begin try 
            match input with
                | "quit" -> (Printf.printf "Quitting.\n"; cond := false)
                | "" -> ()
                | _ -> Printf.printf "=> %s\n" (to_string (eval (parse input) environ))
            with Failure a -> Printf.printf "%s: Unsupported/Not a well-formatted Lisp expression.\n" a
        end
    )
  done
      
let () = read_eval_print_loop ()
