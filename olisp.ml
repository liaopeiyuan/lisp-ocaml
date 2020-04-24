#load "str.cma";;

let debug = false;

(* Either *)
type ('f, 's) e = | F of 'f | S of 's

type symb
type num
type atom
type l
type exp
type env

type 'a ele = E of 'a | L of 'a ele list

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
    let x = Int64.of_string token in Atom( S (Number (F x)))
      with Failure _ -> 
        begin try 
            let y = Float.of_string token in Atom (S (Number (S y)))
          with Failure _ -> Atom(F (Symbol token) )
        end
    end

let rec pl (a: string list) b = if not(debug) then () else match a with
   | [] -> (Printf.printf "%s\n" b; ())
   | x::xs -> (Printf.printf "%s " (x) ; pl xs b)

let rec read_from_tokens (tokens: string list ref) : 'a ele = 
    let () = pl (!tokens) "list" in
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
            L (!result |> List.rev) 
        )
   | ")"::_ -> failwith "unexpected )" 
   | x::xs->  let () = tokens := xs in E (atom(x))

let break(e : 'a ele) : 'a ele list = match e with
    | L a -> a
    | E _ -> failwith "incorrect usage of function"

let parse(program:string) : exp scheme_obj =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens |> break in
    Exp(S (List (result)) )

let _parse(program:string) : 'a ele list =
    let input = program |> tokenize |> ref in
    let result = input |> read_from_tokens |> break in
    result

let literal x = Exp (F (Atom (S (Number (F x))))) 

let basic_environment (_: unit) : env scheme_obj =
    let hs: (symb scheme_obj, store) Hashtbl.t = Hashtbl.create 42 in
    let rec add l = match l with
      | List [] -> literal 0L
      | List (  (E (Atom (S (Number (F a)))) )::xs  ) -> match add(List xs) with
            | Exp (F (Atom (S (Number (F sum))))) ->  literal (Int64.add sum a)
            | _ -> failwith "incorrect usage of add"
    in
    (   
        Hashtbl.add hs (Symbol "+") (Proc add);
        Env hs
    )

(* To Be Implemented *)
let eval (expr) = expr

let Env environ = basic_environment()
let Proc f = Hashtbl.find environ (Symbol "+")
let g x = (E (Atom (S (Number (F x)))) )

let program = "(+ 1 2)"

let a = tokenize(program)

let res = _parse(program) 
let e1::b = res
let e2::d = b