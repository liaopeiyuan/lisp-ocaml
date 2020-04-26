(* Lisp interpreter via GADT and Subtyping *)
(* Inspiration: https://norvig.com/lispy.html *)
(* Author: Peiyuan Liao (alexander_liao@outlook.com) *)

(* Debug *)
let debug = false
let seed = 42

(* Either *)
type ('f, 's) e = | L of 'f | R of 's

type num
type l
type atom = [ `Atom ]
type exp = [ atom | `Exp ] (* An atomic expression can also be an expression *)
type env
type func = [ `Namespace ]
type data = [ `Namespace ] (* by Lisp-1 standard, functions and
                                data share the same namespace *)
type namespace = [ `Namespace ]

(* ragged higher-dimensional array for AST *)
type 'a ast = Leaf of 'a | Node of 'a ast list

(* Scheme objects *)
type 'a scheme_obj =
    | Symbol : string -> data scheme_obj (* Symbols: all non-literal entities 
                                            are stored this way before eval *)
    | Func : (namespace scheme_obj list * exp scheme_obj * env scheme_obj) -> func scheme_obj
            (* params,                 body,            env *)
            (* User-defined procedures *)
    | Number : (int64,float) e -> num scheme_obj (* Numbers: int or float *)
    | T : num scheme_obj (* True as a "boolean" scheme object *)
    | F : num scheme_obj (* False as a "boolean" scheme object *)
    | Atom : (namespace scheme_obj, num scheme_obj) e -> atom scheme_obj (* Atomic expressions *)
    | List : atom scheme_obj ast list -> l scheme_obj (* List of atomic expressions 
                                                        is also an expression *)
    | Exp : (atom scheme_obj, l scheme_obj) e -> exp scheme_obj (* An expression is either
                                                                  an atomic expression by itself
                                                                  or a list of atomic expressions *)
    | Epsilon : exp scheme_obj (* Epsilon to represent the result of commands like "define" *)
    | Env : lookup -> env scheme_obj (* An environment is a scheme object *)
and lookup = (* Scoping *)
    | Innermost of (namespace scheme_obj, store) Hashtbl.t (* Inner-most scope *)
    | Outer of ((namespace scheme_obj, store) Hashtbl.t * lookup)
    (* to deal with anonymous functions, "it" is reserved for anonymous functions *)
and store =  (* Environment-defined procedures, variables, and user-defined procedures *)
    | Proc of (l scheme_obj -> exp scheme_obj) (* Pre-defined procedures (like +) in envs *)
    | Ref of num scheme_obj (* Variable-value bindings *) 
    | UProc of func scheme_obj (* User-defined procedures *)               

(* built-in commands and function to check for them *)
type builtin = Quote | If | Define | Set | Lambda | NotABuiltin

let check_builtin a = match a with
    | (Symbol "quote") -> Quote
    | (Symbol "if") -> If
    | (Symbol "define") -> Define
    | (Symbol "set!") -> Set
    | (Symbol "lambda") -> Lambda
    | _ -> NotABuiltin

(* helper function to convert a child in AST to an expression *)
let atom_ele_to_exp (x : atom scheme_obj ast) : exp scheme_obj = match x with Leaf x' -> Exp (L (x')) | Node x' ->  Exp (R (List x'))

(* quote command *)
let quote (x : atom scheme_obj ast list) : exp scheme_obj = match x with 
    |  [] -> failwith "Invalid quote: (quote) []" 
    |  ((Leaf e)::_) -> Exp (L e) 
    |  ((Node (es))::_)  -> Exp (R (List es))

(* if command *)
let condition (x: exp scheme_obj) (e1: atom scheme_obj ast) (e2: atom scheme_obj ast) :> exp scheme_obj = 
    let condition' x e1 e2 : atom scheme_obj ast =  match x with
            | (Exp (L (Atom (R (F))))) -> e2
            | _ -> e1
    in
    match condition' x e1 e2 with
            | Leaf (e') -> Exp (L (e'))
            | Node (e') -> Exp (R (List (e')))

let lambda (params : atom scheme_obj ast) (body : atom scheme_obj ast list) (env : env scheme_obj) : exp scheme_obj =
    let elem_ns_apply a = match a with
        | Leaf (Atom (L (p))) -> p
        | _ -> failwith "formal parameters can only be namespace entities"
    in
    let params_to_ns params = match params with
        | Leaf (Atom (L (p))) -> [p]
        | Node l -> List.map elem_ns_apply l
        | _ -> failwith "formal parameters can only be namespace entities"
    in
    match (List.rev body) with
        | [] -> failwith "Invalid lambda."
        | (Node l)::_ -> Exp(L (Atom (L(Func (params_to_ns params, Exp (R (List (l))), env)  ))))
        | (Leaf a)::_ ->  Exp(L (Atom (L(Func (params_to_ns params, Exp(L (a)), env)  )))) 

(* tokenize a Lisp expression (in string) to tokens *)
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

(* convert a string to a symbol/literal *)
let atom (token: string) : atom scheme_obj = begin try
    let x = Int64.of_string token in Atom (R (Number (L x)))
    with Failure _ -> 
        begin try 
            let y = Float.of_string token in Atom (R (Number (R y)))
        with Failure _ -> Atom(L (Symbol token) )
        end
    end

(* helper function to print a string list *)
let rec print_list (a: string list) b = if not(debug) then () else match a with
   | [] -> (Printf.printf "%s\n" b; ())
   | x::xs -> (Printf.printf "%s " (x) ; print_list xs b)

(* imperative function to construct AST from tokens *)
let rec read_from_tokens (tokens: string list ref) : 'a ast = 
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
                    Node (!result |> List.rev) 
                )
        | ")"::_ -> failwith "unexpected )" 
        | x::xs->  let () = tokens := xs in Leaf (atom(x))

(* final parser: frpm a string to an expression *)
let parse (program : string) : exp scheme_obj =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens in
    match result with 
        | Node a -> Exp(R (List (a)) )
        | Leaf b -> Exp (L b)
and _parse (program : string) : atom scheme_obj ast list =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens in
    match result with
        | Node a -> a
        | Leaf b -> [Leaf b] 

(* helper functions to convert literals to Scheme objects *)
let literal x = Exp (L (Atom (R (Number (L x))))) 
let float_literal x = Exp (L (Atom (R (Number (R x))))) 

(* basic environments that will hold user defined procedures,
   scopes, variables and pre-defined procedures.
   Implemented functions/bindings: +, pi, list
 *)
let basic_environment (_: unit) : env scheme_obj =
    let hs: (data scheme_obj, store) Hashtbl.t = Hashtbl.create seed in
    let rec add l = match l with
        | List [] -> literal 0L
        | List (  (Leaf (Atom (R (Number (L a)))) )::xs  ) -> (match add(List xs) with
                | Exp (L (Atom (R (Number (L sum))))) ->  literal (Int64.add sum a)
                | Exp (L (Atom (R (Number (R sum))))) ->  float_literal (Int64.to_float(a) +. sum)
                | _ -> failwith "incorrect usage of add")
        | List (  (Leaf (Atom (R (Number (R a)))) )::xs  ) -> (match add(List xs) with
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

(* finding a binding in an environment: starting with the inner-most scope,
   then recursively moves up if not found. If binding does not exist in all
   scopes, raises Not_found exception.
 *)
let rec find (h: env scheme_obj) (key: data scheme_obj) = match h with
    | Env (Innermost hs) -> Hashtbl.find hs key
    | Env (Outer (hs, inner)) -> try (find (Env inner) key) with Not_found -> Hashtbl.find hs key

(* To Be Implemented: Eval *)
let rec eval (e: exp scheme_obj) (env: env scheme_obj ref) : exp scheme_obj = 
    e
(* helper function that prunes a children in AST into an "irreducible" expression,
   given that eval is implemented correctly
 *)
and prune (env: env scheme_obj ref) (x : atom scheme_obj ast) : atom scheme_obj ast =   
    let rec subtl (x': atom scheme_obj ast list) :> atom scheme_obj ast = 
            match (eval (Exp (R (List x'))) env) with  
                | Exp (L x) -> Leaf x 
                | Exp (R (List x)) -> (Node x) 
                | _ -> failwith "sub-expressions not correctly evaluated" in
    let rec subte (x': atom scheme_obj) :> atom scheme_obj ast = 
            match (eval (Exp (L x')) env) with 
                | Exp (L x) -> Leaf x 
                | Exp (R (List x)) -> (Node x) 
                | _ -> failwith "sub-expressions not correctly evaluated" in 
    (match x with | Leaf x' -> (subte x') | Node x' -> (subtl x')) 
(* create a user-defined scope *)
and create_user_env ( (params, args, env) : data scheme_obj list * store list * lookup) : lookup =
    let rec zip params args hs = match ( params,  args) with 
        | ([], []) -> hs
        | (x::xs, y::ys) -> (Hashtbl.add hs x y; zip xs ys hs)
        | _ -> failwith "inproper user defined procedure"
    in
    let hs = Hashtbl.create seed in
    let dict = zip params args hs in
    let rec update_env (env, inner) = match env with
       | Innermost hs -> Outer (hs, inner)
       | Outer (hs, outin) -> Outer (hs, update_env(outin, inner))
    in
    update_env (env, Innermost(dict))
(* evaluate user-defined procedures (since function application won't work) *)
and eval_user_proc (p: func scheme_obj) (args: atom scheme_obj ast list) (env: env scheme_obj): exp scheme_obj =
    let rec to_store_list args = (match args with 
        |  [] -> []
        |  ( (Leaf (Atom (R x)))::xs) -> (Ref x) :: (to_store_list (xs))
        |  ( (Leaf (Atom (L (Func f))))::xs) -> (UProc (Func f)) :: (to_store_list (xs))
        |  ( (Leaf (Atom (L (Symbol s))))::xs) ->  begin try (find env (Symbol s)) :: (to_store_list (xs)) with Not_found -> failwith ("Unbound symbol: "^s) end
        | _ -> failwith "incorrect usage of eval_user_proc")
    in
    match p with
        | (Func (params, body, Env env)) -> eval body (ref (Env (create_user_env(params, to_store_list args, env)))) 
        | _ -> failwith "incorrect usage of eval_user_proc"
        
let environ = ref (basic_environment ())

let program = "((lambda (x y z) (+ x y z)) ((lambda (x) x) 1) 2 (+ 3 4))"

let b = parse "((lambda (x) x) 1) 2 (+ 3 4))"
let a = parse "(lambda (x y z) (+ x y z))"
let program = "((lambda (f x) f x) 1)"

let res = parse(program) 

(*
let helper program = match parse(program) with Exp(R(List (x::xs))) -> (x,xs)
*)

(* turn a num scheme_obj into a string *)
let num_str (n : num scheme_obj) : string = match n with
    | Number (L s) -> Int64.to_string s
    | Number (R s) -> Float.to_string s
    | T -> "#t"
    | F -> "#f"

(* turn an expression into a string *)
let rec to_string (obj: exp scheme_obj) : string =     
    (match obj with
    | Epsilon -> ""
    | Exp (L (Atom (L (Symbol s))))-> s
    | Exp (L (Atom (L (Func _))))-> "#<Closure>"
    | Exp (L (Atom (R (n))))-> num_str (n)
    | Exp (R (List l))-> match l with 
        | [] -> "()"
        | (Leaf (Atom (L (Symbol s))))::xs -> (match (to_string'(xs)) with "" -> "("^s^")" | str -> "("^s^" "^str^")")
        | (Leaf (Atom (L (Func _))))::xs -> (match (to_string'(xs)) with "" -> "(#<Closure>)" | str -> "(#<Closure> "^str^")")
        | (Leaf (Atom (R (n))))::xs ->  (match (to_string'(xs)) with "" -> "("^(num_str (n))^")" | str -> "("^(num_str (n))^" "^str^")")
        | (Node (ll))::xs -> let temp = (to_string(Exp (R (List ll)))) in (match to_string'(xs) with ""-> "("^temp^")" | str ->  "("^temp^" "^str^")")
    )
and to_string' (obj: atom scheme_obj ast list) : string = (match obj with
        | [] -> ""
        | (Leaf (Atom (L (Symbol s))))::xs -> (match to_string'(xs) with "" -> s | str -> s^" "^str)
        | (Leaf (Atom (L (Func _))))::xs -> (match (to_string'(xs)) with "" -> "#<Closure>" | str -> "(#<Closure> "^str^")")
        | (Leaf (Atom (R (n))))::xs -> (match to_string'(xs) with "" -> (num_str  n) | str -> (num_str  n)^" "^str)
        | (Node (ll))::xs -> let temp = ( to_string(Exp (R (List ll))) ) in (match to_string'(xs) with "" -> temp | str -> temp^" "^str))
    
(* Read-Eval-Print-Loop for interface *)
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

(* entry point to program *) 
let () = read_eval_print_loop ()
