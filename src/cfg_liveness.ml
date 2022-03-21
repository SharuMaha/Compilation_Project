open Batteries
open Cfg
open Prog
open Utils

(* Analyse de vivacité *)

(* [vars_in_expr e] renvoie l'ensemble des variables qui apparaissent dans [e]. *)
let rec vars_in_expr (e: expr) =
  match e with 
        |Ebinop(bop, e1, e2) -> Set.union (vars_in_expr e2) (vars_in_expr e1)
        | Eunop (uop, e) -> vars_in_expr e
        | Eint i -> Set.empty
        | Evar s -> Set.singleton s
        | Ecall(str,argl) -> List.fold_left (fun acc exp -> Set.union acc (vars_in_expr exp) ) (Set.singleton str) argl


(* [live_cfg_node node live_after] renvoie l'ensemble des variables vivantes
   avant un nœud [node], étant donné l'ensemble [live_after] des variables
   vivantes après ce nœud. *)
let live_cfg_node (node: cfg_node) (live_after: string Set.t) =
   match node with
   |Cassign(str,exp,i) ->Set.union (Set.diff live_after (Set.singleton str)) (vars_in_expr exp)
   |Creturn(exp) ->Set.union (vars_in_expr exp) live_after
   |Ccmp(exp, i, i2) ->Set.union (vars_in_expr exp) live_after
   |Ccall(str, argl, i) -> Set.union (vars_in_expr (Ecall(str,argl))) live_after
   |_ -> live_after

(* [live_after_node cfg n] renvoie l'ensemble des variables vivantes après le
   nœud [n] dans un CFG [cfg]. [lives] est l'état courant de l'analyse,
   c'est-à-dire une table dont les clés sont des identifiants de nœuds du CFG et
   les valeurs sont les ensembles de variables vivantes avant chaque nœud. *)
let live_after_node cfg n (lives: (int, string Set.t) Hashtbl.t) : string Set.t =
        let suc = succs cfg n in
        Set.fold (fun elt acc ->match Hashtbl.find_option lives elt with |None -> acc|Some vv-> Set.union vv acc) suc Set.empty

(* [live_cfg_nodes cfg lives] effectue une itération du calcul de point fixe.

   Cette fonction met à jour l'état de l'analyse [lives] et renvoie un booléen
   qui indique si le calcul a progressé durant cette itération (i.e. s'il existe
   au moins un nœud n pour lequel l'ensemble des variables vivantes avant ce
   nœud a changé). *)

let live_cfg_nodes cfg (lives : (int, string Set.t) Hashtbl.t) =
        Hashtbl.fold (fun key value acc -> let oldvalue = match Hashtbl.find_option lives key with |None -> Set.empty |Some vale -> vale in
        if Set.equal (live_cfg_node value (live_after_node cfg key lives)) oldvalue then acc else (Hashtbl.replace lives key (live_cfg_node value (live_after_node cfg key lives));true)) cfg false

(*
let live_cfg_nodes cfg (lives : (int, string Set.t) Hashtbl.t) =
   Hashtbl.fold (fun idx node acc ->
      let oldInSet =
      match Hashtbl.find_option lives idx with
      | None -> Set.empty
      | Some set -> set in
      let newInSet = live_cfg_node node (live_after_node cfg idx lives) in
      if Set.equal newInSet oldInSet then acc
      else (Hashtbl.replace lives idx newInSet; true)
      )
      cfg
      false
*)

(* [live_cfg_fun f] calcule l'ensemble des variables vivantes avant chaque nœud
   du CFG en itérant [live_cfg_nodes] jusqu'à ce qu'un point fixe soit atteint.
   *)
let live_cfg_fun (f: cfg_fun) : (int, string Set.t) Hashtbl.t =
  let lives = Hashtbl.create 17 in

  let rec prochain () =
          match live_cfg_nodes f.cfgfunbody lives with
          |false -> ()
          |true -> prochain ()
  in
  prochain ();lives
