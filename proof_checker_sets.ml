type form = 
  |Top
  |Bot
  |Var of string
  |Not of form
  |And of form * form
  |Or of form * form
  |Imply of form * form


let rec form_is_equal (g:form)(h:form) : bool = 
  (* Teste l'égalité syntaxique(et pas structurelle, à la différence du (=))*)
  match f, g with 
  | Top,Top 
  | Bot,Bot -> true
  | Var(x),Var(y) -> x=y
  | Not(g'),Not(h')-> form_is_equal g' h'
  | And(x1,y1),And(x2,y2) 
  | Or(x1,y1),Or(x2,y2)
  | Imply(x1,y1),Imply(x2,y2) -> (form_is_equal x1 x2) && (form_is_equal y1 y2)

type sequent = { prem : form Set.t ; conc : form} 

type arbre_preuve = { name:string ; s : sequent; l : arbre_preuve Set.t}

(* La fonction suivante vérifie la correction*)
let rec check (a:arbre_preuve) : bool = 
  (* Essaye de reconnaître une règle de la logique intuitionniste*)
  begin match a.name with
  | "ax" -> Set.mem a.s.conc a.s.prem && Set.is_empty a.l
  | "topi" -> a.s.conc = Top && Set.is_empty a.l
  | "bote" -> begin match a.l with 
    | Set.singleton t1 -> t1.s.conc = Bot  && Set.equal t1.s.prem a.s.prem
    | _ -> false end
  | "oui" -> begin match a.l with 
    | Set.singleton t1 -> begin match a.s.conc with 
      |Or(x,y) -> (form_is_equal t1.s.conc x || form_is_equal t1.s.conc y) && Set.equal t1.s.prem a.s.prem
      | _ -> false end
    | _ -> false end   
  | "eti" -> begin match a.l with 
    | [t1;t2] -> begin match a.s.conc with 
      |And(x,y) -> ((t1.s.conc = x && t2.s.conc = y) || (t1.s.conc = y && t2.s.conc = x)) 
        && t1.s.prem = a.s.prem && t2.s.prem = a.s.prem
      | _ -> false end
    | _ -> false end   
  | "noni" -> begin match a.l with
    | Set.singleton t1 -> begin match a.s.conc with 
      | Not(g) -> t1.conc = Bot && Set.equal t1.prem (Set.union a.s.prem (Set.singleton g))
      | _ -> false end
    | _ -> false end
  | _ -> false 
  end 
  && List.for_all check a.l

let print_bool b = 
  if b then Printf.printf "true" else Printf.printf "false"

let main = 
  let p = Var("p") in 
  let s1 = {prem = [p]; conc = p} in 
  let a = {name = "ax" ; s = s1; l = []} in 
  let g = Or(Var("p"), Var("q")) in
  let s2 = {prem = [p]; conc = g} in 
  let a2 = {name = "oui"; s = s2; l = [a]}
  print_bool (check a)

