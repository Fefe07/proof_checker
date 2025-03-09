type form = 
  | Top
  | Bot
  | Var of string
  | Not of form
  | And of form * form
  | Or of form * form
  | Imply of form * form



type arbre_preuve = { name:string ; premisses : form list ; conclusion : form; l:arbre_preuve list}

(* La fonction suivante vérifie la correction*)
let rec check (a:arbre_preuve) : bool = 
  (* Essaye de reconnaître une règle de la logique intuitionniste*)
  begin match a.name with
  | "Ax" -> (List.exists (fun f -> f = a.conclusion) a.premisses ) && a.l = []
  | "TopI" -> a.conclusion = Top && a.l = []
  | "BotE" -> begin match a.l with 
		| [t1] -> t1.conclusion = Bot  && t1.premisses = a.premisses
		| _ -> false end
  | "OrI" -> begin match a.l with 
		| [t1] -> begin match a.conclusion with 
			|Or(x,y) -> (t1.conclusion = x || t1.conclusion = y) && t1.premisses = a.premisses
			| _ -> false end
		| _ -> false end   
  | "AndI" -> begin match a.l with 
		| [t1;t2] -> begin match a.conclusion with 
	  	|And(x,y) -> ((t1.conclusion = x && t2.conclusion = y) || (t1.conclusion = y && t2.conclusion = x)) 
			&& t1.premisses = a.premisses && t2.premisses = a.premisses
	  	| _ -> false end
		| _ -> false end   
  | "NotI" -> begin match a.l with
		| [t1] -> begin match t1.premisses with 
			| phi :: gamma -> Not(phi) = a.conclusion && gamma = a.premisses && t1.conclusion = Bot
			| _ -> false end
		| _ -> false end
  | "ImplyI" -> begin match a.l with 
		| [t1] -> begin match t1.premisses with 
			| phi :: gamma -> a.conclusion = Imply(phi,t1.conclusion) && gamma = a.premisses
			| _ -> false end 
		| _ -> false end 
	| "NotE" -> begin match a.l with 
		| [t1;t2] -> 
			a.conclusion = Bot
			&& t1.premisses = t2.premisses
			&& (t1.conclusion = Not(t2.conclusion) 
			|| t2.conclusion = Not(t1.conclusion))
		| _ -> false end
	| "AndE" -> begin match a.l with
		| [t1] -> begin match t1.conclusion with
			| And(f,g) -> f = a.conclusion || g = a.conclusion && a.premisses = t1.premisses
			| _ -> false end
		| _ -> false end
	(* | "OrE" -> begin match a.l with 
		| [t1;t2;t3] -> begin match t1. *)
  | _ -> false 
  end 
  && List.for_all check a.l

let print_bool b = 
  if b then Printf.printf "true" else Printf.printf "false"

let () = 
  let p = Var("p") in 
  let a = {name = "Ax" ; premisses = [p]; conclusion = p; l = []} in 
  let g = Or(Var("p"), Var("q")) in 
  let a2 = {name = "OrI"; premisses = [p]; conclusion = g; l = [a]} in
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

let print_token (t : token) : unit = 
	match t with
	| LParen -> Printf.printf "LParen\n"
	| RParen -> Printf.printf "RParen\n"
	| LBracket -> Printf.printf "LBracket\n"
	| RBracket -> Printf.printf "RBracket\n"
	| Colon -> Printf.printf "Colon\n"
  | Comma -> Printf.printf "Comma\n"
  | Semicolon -> Printf.printf "Semicolon\n"
	| VarID(s) -> Printf.printf "VarID(%s)\n" s	
	| Identifier(s) -> Printf.printf "Identifier(%s)\n" s


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
		| '\n' :: s'
		| '\t' :: s'
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
  lexer_rec (List.of_seq (String.to_seq s))


let test = "Proof(Hyp : {p,Not(p)}; Conc : Bot) 
	NotE(p) 
		Ax
		Ax"


(* Ces deux defs sont equivalentes *)
let (let$) = Option.bind

let (let$) value cont =
  match value with
  | None -> None
  | Some x -> cont x 

(* Assert pred *)
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

(* Bouffe le RBracket mais c'est pas grave *)
let rec read_form (l' : token list ref) : form option =
	let$ truc = next l' in
	match truc with
	| Comma -> read_form l'
	| Identifier("Top") -> Some(Top)
  | Identifier("Bot") -> Some(Bot)
	| VarID(p) -> Some(Var(p)) 
	| Identifier("Not") -> begin 
		let$ truc = next l' in 
		let+ __ = (truc = LParen) in 
		let$ g = read_form l' in
		let$ truc = next l' in
		let+ __ = (truc = RParen) in 
		Some(Not(g)) 
		end
	| Identifier("And") -> begin 
		let$ truc = next l' in 
		let+ __ = (truc = LParen) in 
		let$ g = read_form l' in
		let$ truc = next l' in
		let+ __ = (truc = Comma) in
		let$ h = read_form l' in 
		let$ truc = next l' in
		let+ __ = (truc = RParen) in 
		Some(And(g,h)) 
		end
	| Identifier("Or") -> begin 
		let$ truc = next l' in 
		let+ __ = (truc = LParen) in 
		let$ g = read_form l' in
		let$ truc = next l' in
		let+ __ = (truc = Comma) in
		let$ h = read_form l' in 
		let$ truc = next l' in
		let+ __ = (truc = RParen) in 
		Some(Or(g,h)) 
		end
	| Identifier("Imply") -> begin 
		let$ truc = next l' in 
		let+ __ = (truc = LParen) in 
		let$ g = read_form l' in
		let$ truc = next l' in
		let+ __ = (truc = Comma) in
		let$ h = read_form l' in 
		let$ truc = next l' in
		let+ __ = (truc = RParen) in 
		Some(Imply(g,h)) 
		end
	| _ -> None


exception Finished
let read_form_list (l':token list ref) : form list option = 
	let$ truc = next l' in 
	let+ __ = (truc = Colon) in
	let$ truc = next l' in 
	let+ __ = (truc = LBracket) in
	Printf.printf "Coucou_rfl\n" ;
	let liste = ref [] in
	try
		while true do 
			match read_form l' with
			| Some(g) -> liste:= g :: !liste ; 
			| None -> raise Finished
		done 
	with 
	| Finished -> Some !liste
				

let parser (l : token list) : arbre_preuve option =
	(* Renvoie None en cas d'échec *)
	let l' = ref l in
	let$ truc = next l' in 
	let+ __ = (truc = Identifier("Proof")) in
	(* Printf.printf "Coucou\n" ; *)
	let$ truc = next l' in 
	let+ __ = (truc = LParen) in
	let$ truc = next l' in 
	let+ __ = (truc = Identifier("Hyp")) in
	(* Printf.printf "Coucou\n" ; *)
	let$ hyps = read_form_list l' in
	(* Pas besoin de lire le RBrakcet, il a été bouffé par le read_form_list*)
	(* Printf.printf "Coucou\n" ; *)
	let$ truc = next l' in 
	let+ __ = (truc = Semicolon) in
	(* Printf.printf "Coucou\n" ; *)
	let$ truc = next l' in 
	let+ __ = (truc = Identifier("Conc")) in
	(* Printf.printf "Coucou\n" ; *)
	let$ truc = next l' in 
	let+ __ = (truc = Colon) in
	(* Printf.printf "Coucou\n" ; *)
	let$ conc = read_form l' in 
	let$ truc = next l' in 
	let+ __ = (truc = RParen) in
	Printf.printf "On a lu les hypotheses et conclusions :)\n" ;

	let rec lire_arbre (hypotheses : form list)(conclusion : form) : arbre_preuve option =
		let$ regle = next l' in
		match regle with
		| Identifier("NotE") -> begin
			let$ truc = next l' in 
			let+ __ = (truc = LParen) in
			let$ form = read_form l' in
			let$ truc = next l' in 
			let+ __ = (truc = RParen) in
			let$ arbre1 = lire_arbre hypotheses form in
			let$ arbre2 = lire_arbre hypotheses (Not(form)) in
			Some({name = "NotE"; premisses = hypotheses ; conclusion = conclusion; l = [arbre1;arbre2]})
		end
		| Identifier("Ax") -> Some({name = "Ax";premisses = hypotheses ; conclusion = conclusion; l = []})
		| _ -> None
	in
	lire_arbre hyps conc



