
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
    let (name,s') = aux s in VarID(String.of_seq(List.to_seq name))::lexer_rec s'
  and read_ID (s : char list) : token list =
    let rec aux (s : char list) : (char list)*(char list) = 
      match s with
      | ('a'..'z' as l) :: s' 
      | ('A'..'Z' as l) :: s' -> let (a,b) = aux s' in (l::a,b)
      | _ -> ([],s)
    in
    let (name,s') = aux s in Identifier(String.of_seq(List.to_seq name))::lexer_rec s'
  in
  List.rev (lexer_rec(List.of_seq(String.to_seq s)))




type syntax_tree
  | Proof of syntax_tree * syntax_tree (*Args and body*)
  | Args of syntax_tree * syntax_tree (*Hyp and conc*)
  | Hyp of 


let parser (l : token list) : 