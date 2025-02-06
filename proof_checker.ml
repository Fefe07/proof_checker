type form = 
  | Top
  | Bot
  | Var of string
  | Not of form
  | And of form * form
  | Or of form * form
  | Imply of form * form

type sequent = { premisses : form list ; conclusion : form} 

type arbre_preuve = { name:string ; s:sequent; l:arbre_preuve list}

(* La fonction suivante vérifie la correction*)
let rec check (a:arbre_preuve) : bool = 
  (* Essaye de reconnaître une règle de la logique intuitionniste*)
  begin match a.name with
  | "ax" -> (List.exists (fun f -> f = a.s.conclusion) a.s.premisses ) && a.l = []
  | "topi" -> a.s.conclusion = Top && a.l = []
  | "bote" -> begin match a.l with 
	| [t1] -> t1.s.conclusion = Bot  && t1.s.premisses = a.s.premisses
	| _ -> false end
  | "oui" -> begin match a.l with 
	| [t1] -> begin match a.s.conclusion with 
	  |Or(x,y) -> (t1.s.conclusion = x || t1.s.conclusion = y) && t1.s.premisses = a.s.premisses
	  | _ -> false end
	| _ -> false end   
  | "eti" -> begin match a.l with 
	| [t1;t2] -> begin match a.s.conclusion with 
	  |And(x,y) -> ((t1.s.conclusion = x && t2.s.conclusion = y) || (t1.s.conclusion = y && t2.s.conclusion = x)) 
		&& t1.s.premisses = a.s.premisses && t2.s.premisses = a.s.premisses
	  | _ -> false end
	| _ -> false end   
  | "noni" -> begin match a.l with
	| [t1] -> begin match t1.s.premisses with 
	  | phi :: gamma -> Not(phi) = a.s.conclusion && gamma = a.s.premisses && t1.s.conclusion = Bot
	  | _ -> false end
	| _ -> false end
  | "impli" -> begin match a.l with 
	| [t1] -> begin match t1.s.premisses with 
	  | phi :: gamma -> a.s.conclusion = Imply(phi,t1.s.conclusion) && gamma = a.s.premisses
	  | _ -> false end 
	| _ -> false end 
  | _ -> false 
  end 
  && List.for_all check a.l

let print_bool b = 
  if b then Printf.printf "true" else Printf.printf "false"

let () = 
  let p = Var("p") in 
  let s1 = {premisses = [p]; conclusion = p} in 
  let a = {name = "ax" ; s = s1; l = []} in 
  let g = Or(Var("p"), Var("q")) in
  let s2 = {premisses = [p]; conclusion = g} in 
  let a2 = {name = "oui"; s = s2; l = [a]} in
  print_bool (check a2) ;
  print_newline ()


  type token =
	| LParen
	| RParen
	| LBracket
	| RBracket
	| Colon
  | Comma
  | Semicolon
	| VarID of string				(* Variable de la logique *)
	| Identifier of string	(* Constructeur logique ou règle d'inférence *)



let lexer (s : string) : token list = 
	let rec lexer_rec (s : char list) : token list = 
		match s with
		| [] -> []
		| '(' :: s' -> LParen :: lexer_rec s'
		| ')' :: s' -> RParen :: lexer_rec s'
		| '{' :: s' -> LBracket :: lexer_rec s'
		| '}' :: s' -> RBracket :: lexer_rec s'
		| ':' :: s' -> Colon :: lexer_rec s' 
		| ',' :: s' -> Comma :: lexer_rec s'
		| ';' :: s' -> Semicolon :: lexer_rec s'
		| ' ' :: s' -> lexer_rec s'
		| 'a'..'z' :: _ -> read_var s 
		| 'A'..'Z' :: _ -> read_ID s 
		| _ -> failwith "caractere inconnu"
	and read_var (s : char list) : token list =
		let rec aux (s : char list) : char list * char list = 
			match s with 
			|('a'..'z' as l) :: s' ->  let (a,b) = aux s' in (l::a,b)
			| _ -> ([],s)
		in
		let (name,s') = aux s in 
		VarID(String.of_seq(List.to_seq name))::lexer_rec s'
  and read_ID (s : char list) : token list =
	let rec aux (s : char list) : (char list)*(char list) = 
		match s with
		| ('a'..'z' as l) :: s' 
		| ('A'..'Z' as l) :: s' -> let (a,b) = aux s' in (l::a,b)
		| _ -> ([],s)
	in
	let (name,s') = aux s in 
	Identifier(String.of_seq(List.to_seq name))::lexer_rec s'
  in
  List.rev (lexer_rec(List.of_seq(String.to_seq s)))


let (let*) = Option.bind

let (let*) value cont =
  match value with
  | None -> None
  | Some x -> cont x

let (let+) pred cont =
  if pred then cont () else None


(* let read(t: token)(l:token list) : token list = 
	match l with 
	| [] -> failwith "liste de tokens vide"
	| a :: l' when t = a -> l'
	| _ -> failwith "erreur de syntaxe"  *)

let next (stream: 'a list ref): 'a option =
	match !stream with
	| [] -> None
	| head :: tail ->
		stream := tail;
		Some head

let parser (l : token list) : arbre_preuve option =
	let proof = read Identifier("Proof") l in 
	let l = read LParen l in 
	let l = read Identifier("Hyp") in 
	let* var = next (??) in
	let+ __ = (var = LParen) in
	...
	blabla;

(fun var -> blabla)
