let debug = false;

(* Either *)
type ('f, 's) e = | L of 'f | R of 's

type symb
type num
type atom
type l
type exp
type env

type 'a ele = Ele of 'a | Li of 'a ele list

type 'a scheme_obj =
    | Symbol : string -> symb scheme_obj
    | Number : (int64,float) e -> num scheme_obj
    | Atom : (symb scheme_obj, num scheme_obj) e -> atom scheme_obj
    | List : atom scheme_obj ele list -> l scheme_obj
    | Exp : (atom scheme_obj, l scheme_obj) e -> exp scheme_obj
    | Env : lookup -> env scheme_obj
and store = 
    | Proc of (l scheme_obj -> exp scheme_obj) 
    | Ref of num scheme_obj
    | UserDefProc of (l scheme_obj * l scheme_obj * env scheme_obj)
and lookup =
    | Innermost of (symb scheme_obj, store) Hashtbl.t
    | Outer of ((symb scheme_obj, store) Hashtbl.t * lookup)

let rec tokenize(chars: string) : string list = 
    let split = Str.split (Str.regexp "[ \t]+") in
    let explode s = List.init (String.length s) (String.get s) in
    let replace s = List.fold_left (fun x y -> let c = Char.escaped y in match c with "(" -> x^"( " | ")" -> x^" )"|_ -> x^c ) "" s in
    chars |> explode |> replace |> split

let atom (token: string) : atom scheme_obj = begin try
    let x = Int64.of_string token in Atom( R (Number (L x)))
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

exception Break of atom scheme_obj
let break(e : atom scheme_obj ele) : atom scheme_obj ele list = match e with
    | Li a -> a
    | Ele b -> raise (Break b) 

let parse (program:string) : exp scheme_obj =
    let input = program |> tokenize |> ref in
    begin try
    let result = input |> read_from_tokens |> break in
        Exp(R (List (result)) )
        with Break b -> Exp (L b)
    end
        

let _parse(program:string) : atom scheme_obj ele list =
    let input = program |> tokenize |> ref in
    begin try
    let result = input |> read_from_tokens |> break in
     result
     with Break b -> [Ele b]
    end

let literal x = Exp (L (Atom (R (Number (L x))))) 
let float_literal x = Exp (L (Atom (R (Number (R x))))) 
let to_hs (s) : (symb scheme_obj, store) Hashtbl.t = match s with (Env (Innermost hs)) -> hs 

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
    let quote = Proc (fun x -> match x with 
                                | List [] -> failwith "Invalid quote: (quote) []" 
                                | List ((Ele e)::_) ->Exp (L e) 
                                | List ((Li es)::_)  -> Exp (R (List es)) ) 
    in
    let listify = Proc (fun x -> Exp (R x)) in
    (   
        Hashtbl.add hs (Symbol "+") (Proc add);
        Hashtbl.add hs (Symbol "pi") pi;
        Hashtbl.add hs (Symbol "quote") quote;
        Hashtbl.add hs (Symbol "list") listify;
        Env (Innermost hs)
    )

let num_str (n : num scheme_obj) = match n with
    | Number (L s) -> Int64.to_string s
    | Number (R s) -> Float.to_string s

let to_string (obj: exp scheme_obj) : string = match obj with
    | Exp (L (Atom (L (Symbol s))))-> s
    | Exp (L (Atom (R (Number n))))-> num_str (Number n)


(* To Be Implemented *)
let eval (e: exp scheme_obj) (env: env scheme_obj ref) = e

let environ = basic_environment ()
let Env (Innermost env) = environ


let Proc f = Hashtbl.find env (Symbol "+")

let g x = (Ele (Atom (R (Number (L x)))) )
let g2 x = (Ele (Atom (R (Number (R x)))) )

let c = (List [ Li [ Li [Ele( Atom(L(Symbol "+")))]; Ele( Atom(L(Symbol "+"))) ]; Ele( Atom(L(Symbol "+")))  ])
let d = (List [ Li [ Li [Ele( Atom(L(Symbol "+")))]; Ele( Atom(L(Symbol "+"))) ] ])

let program = "(define (merge L M) (if (null? L) M (if (null? M) L (if (< (car L) (car M)) (cons (car L) (merge (cdr L) M)) (cons (car M) (merge (cdr M) L))))))"
let program = "(1 2)"

let a = tokenize(program)

let res = _parse(program) 
let res2 = parse(program) 


(*

let read_eval_print_loop () : unit =
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
                | _ -> Printf.printf "%s\n" (to_string (eval (parse input) environ))
            with Failure "incorrect usage of function" -> Printf.printf "Unsupported/Not a well-formatted Lisp expression.\n"
        end
    )
  done
      

let () = read_eval_print_loop ()
*)