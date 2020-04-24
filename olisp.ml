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
    | Env : (symb scheme_obj, store) Hashtbl.t -> env scheme_obj
and store = 
    | Proc of (l scheme_obj -> exp scheme_obj) 
    | Ref of num scheme_obj

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

let break(e : 'a ele) : 'a ele list = match e with
    | Li a -> a
    | Ele _ -> failwith "incorrect usage of function"

let parse(program:string) : exp scheme_obj =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens |> break in
    match result with 
       | [] -> Exp (R (List []))
       | (Ele x)::[] -> Exp(L (x))
       | _ -> Exp(R (List (result)) )

let _parse(program:string) : 'a ele list =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens |> break in
    result

let literal x = Exp (L (Atom (R (Number (L x))))) 
let float_literal x = Exp (L (Atom (R (Number (R x))))) 
let to_hs (s) : (symb scheme_obj, store) Hashtbl.t = match s with (Env hs) -> hs 

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
                                | List (y::_) -> match y with 
                                                | Ele e -> Exp (L e) 
                                                | Li es -> Exp (R (List es)) ) 
    in
    let listify = Proc (fun x -> Exp (R x)) in
    (   
        Hashtbl.add hs (Symbol "+") (Proc add);
        Hashtbl.add hs (Symbol "pi") pi;
        Hashtbl.add hs (Symbol "quote") quote;
        Hashtbl.add hs (Symbol "list") listify;
        Env hs
    )

(* To Be Implemented *)
let eval (e: exp scheme_obj) (env: env scheme_obj) = failwith "NotImplemented"

let environ = basic_environment()
let Env env = environ
let Proc f = Hashtbl.find env (Symbol "+")
let g x = (Ele (Atom (R (Number (L x)))) )
let g2 x = (Ele (Atom (R (Number (R x)))) )

let c = (List [ Li [ Li [Ele( Atom(L(Symbol "+")))]; Ele( Atom(L(Symbol "+"))) ]; Ele( Atom(L(Symbol "+")))  ])
let d = (List [ Li [ Li [Ele( Atom(L(Symbol "+")))]; Ele( Atom(L(Symbol "+"))) ] ])

let program = "(define (merge L M) (if (null? L) M (if (null? M) L (if (< (car L) (car M)) (cons (car L) (merge (cdr L) M)) (cons (car M) (merge (cdr M) L))))))"
let program = "(pi)"

let a = tokenize(program)

let res = _parse(program) 
let res2 = parse(program) 
