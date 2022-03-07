open Elang
open Batteries
open BatList
open Prog
open Utils
open Builtins
open Utils

let binop_bool_to_int f x y = if f x y then 1 else 0

(* [eval_binop b x y] évalue l'opération binaire [b] sur les arguments [x]
   et [y]. *)
let eval_binop (b: binop) : int -> int -> int =
  match b with
   |Eadd -> fun x y -> x+y
   |Emul -> fun x y -> x*y
   |Emod -> fun x y -> x mod y
   |Exor -> fun x y -> x lxor y
   |Ediv -> fun x y -> x/y
   |Esub -> fun x y -> x-y
   |Eclt -> fun x y -> binop_bool_to_int (fun a b -> a<b) x y
   |Ecle -> fun x y -> binop_bool_to_int (fun a b -> a<=b) x y
   |Ecgt -> fun x y -> binop_bool_to_int (fun a b -> a>b) x y
   |Ecge -> fun x y -> binop_bool_to_int (fun a b -> a>=b) x y
   |Eceq -> fun x y -> binop_bool_to_int (fun a b -> a=b) x y
   |Ecne -> fun x y -> binop_bool_to_int (fun a b -> a<>b) x y 

(* [eval_unop u x] évalue l'opération unaire [u] sur l'argument [x]. *)
let eval_unop (u: unop) : int -> int =
  match u with
   |Eneg -> fun x -> -x

(* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
   erreur si besoin. *)
exception Foo of string
let rec eval_eexpr st (e : expr) : int res =
   match e with
   |Eunop(un,exp) -> eval_eexpr st exp >>= fun evaleres -> OK(eval_unop un evaleres)
   |Eint(inte) -> OK inte
   |Evar(s) -> (match Hashtbl.find_option st.env s with |Some intres -> OK(intres) |_ -> Error "Unknown variable a")
   |Ebinop(bop,e1,e2) ->eval_eexpr st e1 >>= fun e1res -> eval_eexpr st e2 >>= fun e2res ->Printf.printf "%d %d\n" e1res e2res; OK (eval_binop bop e1res e2res)
(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
let rec eval_einstr oc (st: int state) (ins: instr) :
  (int option * int state) res =
   match ins with
   |Iassign(str,exp) -> eval_eexpr st exp>>= fun intres -> let x=Hashtbl.replace st.env str intres in OK(None,st)
   |Iif(exp,ins1,ins2) -> eval_eexpr st exp >>= fun ifres -> Printf.printf "%d\n" ifres;(match ifres with |0 -> eval_einstr oc st ins2 |_ -> eval_einstr oc st ins1)
   |Iwhile(exp, ins1) ->Printf.printf "oupsi\n"; eval_eexpr st exp >>= fun whileres -> (match whileres with |0 ->OK(None, st) |_-> eval_einstr oc st (Iblock(ins1::ins::[])))
(*   |Iblock(instrl) -> List.fold_left (fun acc elt -> (match acc with |OK (intopt,st1) ->  eval_einstr oc st1 elt|_ -> failwith "oulah, tu vas t'amuser a debugger ca")) (OK(None,st)) instrl *)
   |Iblock([]) -> OK(None,st)
   |Iblock(ins1::rinstr) -> eval_einstr oc st ins1 >>= fun insres1 -> (match fst insres1 with |None -> eval_einstr oc (snd insres1) (Iblock(rinstr))|Some ret -> OK insres1 )
   |Ireturn(exp) -> eval_eexpr st exp >>= fun expres -> OK(Some expres, st) 
   |Iprint(exp) -> eval_eexpr st exp >>= fun expres -> Format.fprintf oc "%d\n" expres; OK(None,st)
(*   |Iprint(exp) -> OK(None,st) *)

(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
let eval_efun oc (st: int state) ({ funargs; funbody}: efun)
    (fname: string) (vargs: int list)
  : (int option * int state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restore l'environnement de l'appelant. *)
  let env_save = Hashtbl.copy st.env in
  let env = Hashtbl.create 17 in
  match List.iter2 (fun a v -> Hashtbl.replace env a v) funargs vargs with
  | () ->
    eval_einstr oc { st with env } funbody >>= fun (v, st') ->
    OK (v, { st' with env = env_save })
  | exception Invalid_argument _ ->
    Error (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n"
             fname (List.length vargs) (List.length funargs)
          )

(* [eval_eprog oc ep memsize params] évalue un programme complet [ep], avec les
   arguments [params].

   Le paramètre [memsize] donne la taille de la mémoire dont ce programme va
   disposer. Ce n'est pas utile tout de suite (nos programmes n'utilisent pas de
   mémoire), mais ça le sera lorsqu'on ajoutera de l'allocation dynamique dans
   nos programmes.

   Renvoie:

   - [OK (Some v)] lorsque l'évaluation de la fonction a lieu sans problèmes et renvoie une valeur [v].

   - [OK None] lorsque l'évaluation de la fonction termine sans renvoyer de valeur.

   - [Error msg] lorsqu'une erreur survient.
   *)
let eval_eprog oc (ep: eprog) (memsize: int) (params: int list)
  : int option res =
  let st = init_state memsize in
  find_function ep "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length f.funargs in
  let params = take n params in
  eval_efun oc st f "main" params >>= fun (v, st) ->
  match v with
  |Some a -> OK v
  |None -> Error "your prog is useless, dude"
