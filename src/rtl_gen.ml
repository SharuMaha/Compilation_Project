open Batteries
open Elang
open Cfg
open Rtl
open Prog
open Utils
open Report
open Rtl_print
open Options

(* Une partie de la génération de RTL consiste à allouer les variables dans des
   pseudo-registres RTL.

   Ces registres sont en nombre illimité donc ce problème est facile.

   Étant donnés :
   - [next_reg], le premier numéro de registre disponible (pas encore alloué à
   une variable)
   - [var2reg], une liste d'associations dont les clés sont des variables et les
   valeurs des numéros de registres
   - [v] un nom de variable (de type [string]),

   [find_var (next_reg, var2reg) v] renvoie un triplet [(r, next_reg, var2reg)]:

   - [r] est le registre RTL associé à la variable [v]
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.

*)
let find_var (next_reg, var2reg) v =
  match List.assoc_opt v var2reg with
    | Some r -> (r, next_reg, var2reg)
    | None -> (next_reg, next_reg + 1, (v,next_reg)::var2reg)

(* [rtl_instrs_of_cfg_expr (next_reg, var2reg) e] construit une liste
   d'instructions RTL correspondant à l'évaluation d'une expression E.

   Le retour de cette fonction est un quadruplet [(r,l,next_reg,var2reg)], où :
   - [r] est le registre RTL dans lequel le résultat de l'évaluation de [e] aura
     été stocké
   - [l] est une liste d'instructions RTL.
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.
*)
let rec rtl_instrs_of_cfg_expr (next_reg, var2reg) (e: expr) =
  match e with
  | Ebinop (b, e1, e2) ->
    let ret_reg, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e1 in
    let ret_reg2, l2, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e2 in
    (next_reg, Rbinop (b, next_reg, ret_reg, ret_reg2) ::l@l2, next_reg +1, var2reg )
  | Eunop (u, e) ->
    let ret_reg, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
    (next_reg, Runop(u, next_reg, ret_reg)::l, next_reg +1, var2reg)
  | Eint i ->
    (next_reg, [Rconst(next_reg, i)], next_reg +1, var2reg)
  | Evar v ->
    let r, next_reg, var2reg = find_var (next_reg, var2reg) v in (r, [], next_reg, var2reg)
  | Ecall (fname, e_list) ->
    let (l, next_reg, var2reg),rargs = List.fold_left_map (
      fun (l, next_reg, var2reg) cfg_expr ->
        let (ret, inst, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) cfg_expr in
        ((inst @ l, next_reg, var2reg), ret)
        ) ([], next_reg, var2reg) e_list in
    (next_reg, Rcall (Some next_reg, fname, rargs) :: l, next_reg +1, var2reg)


let is_cmp_op =
  function Eclt -> Some Rclt
         | Ecle -> Some Rcle
         | Ecgt -> Some Rcgt
         | Ecge -> Some Rcge
         | Eceq -> Some Rceq
         | Ecne -> Some Rcne
         | _ -> None

let rtl_cmp_of_cfg_expr (e: expr) =
  match e with
  | Ebinop (b, e1, e2) ->
    (match is_cmp_op b with
     | None -> (Rcne, e, Eint 0)
     | Some rop -> (rop, e1, e2))
  | _ -> (Rcne, e, Eint 0)


let rtl_instrs_of_cfg_node ((next_reg:int), (var2reg: (string*int) list)) (c: cfg_node) =
  match c with
  | Cassign(v, e, s) ->
    let ret_reg, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
    let r, next_reg, var2reg = find_var (next_reg, var2reg) v in
    (Rjmp s :: Rmov(r, ret_reg)::l, next_reg, var2reg)
  | Ccmp(e, s, s2) ->
    let cmp, e1, e2 = rtl_cmp_of_cfg_expr e in
    let ret_reg, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e1 in
    let ret_reg2, l2, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e2 in
    ( Rjmp s2 :: Rbranch(cmp, ret_reg, ret_reg2, s) ::l@l2, next_reg, var2reg)
  | Creturn e ->
    let ret_reg, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
    (Rret(ret_reg)::l, next_reg, var2reg)
  | Cnop s -> ([Rjmp s], next_reg, var2reg)
  | Ccall( fname, e_list, s) ->
    let (l, next_reg, var2reg),rargs = List.fold_left_map (
      fun (l, next_reg, var2reg) cfg_expr ->
        let (ret, inst, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) cfg_expr in
        ((inst @ l, next_reg, var2reg), ret)
        ) ([], next_reg, var2reg) e_list in
    (Rjmp s :: Rcall (None, fname, rargs) :: l, next_reg +1, var2reg)


let rtl_instrs_of_cfg_fun cfgfunname ({ cfgfunargs; cfgfunbody; cfgentry }: cfg_fun) =
  let (rargs, next_reg, var2reg) =
    List.fold_left (fun (rargs, next_reg, var2reg) a ->
        let (r, next_reg, var2reg) = find_var (next_reg, var2reg) a in
        (rargs @ [r], next_reg, var2reg)
      )
      ([], 0, []) cfgfunargs
  in
  let rtlfunbody = Hashtbl.create 17 in
  let (next_reg, var2reg) = Hashtbl.fold (fun n node (next_reg, var2reg)->
      let (l, next_reg, var2reg) = rtl_instrs_of_cfg_node (next_reg, var2reg) node in
      Hashtbl.replace rtlfunbody n (List.rev l);
      (next_reg, var2reg)
    ) cfgfunbody (next_reg, var2reg) in
  {
    rtlfunargs = rargs;
    rtlfunentry = cfgentry;
    rtlfunbody;
    rtlfuninfo = var2reg;
  }

let rtl_of_gdef funname = function
    Gfun f -> Gfun (rtl_instrs_of_cfg_fun funname f)

let rtl_of_cfg cp = List.map (fun (s, gd) -> (s, rtl_of_gdef s gd)) cp

let pass_rtl_gen cfg =
  let rtl = rtl_of_cfg cfg in
  dump !rtl_dump dump_rtl_prog rtl
    (fun file () -> add_to_report "rtl" "RTL" (Code (file_contents file)));
  OK rtl
