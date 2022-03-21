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


let eval_eprog oc (ep: eprog) (memsize: int) (params: int list)
  : int option res =

let rec eval_eexpr st (e : expr) : (int * int state) res  =
   match e with
   |Eunop(un,exp) -> eval_eexpr st exp >>= fun evaleres -> OK(eval_unop un (fst evaleres),st)
   |Eint(inte) -> OK (inte,st)
   |Evar(s) -> (match Hashtbl.find_option st.env s with |Some intres -> OK(intres,st) |_ -> Error "Unknown variable a")
   |Ebinop(bop,e1,e2) ->eval_eexpr st e1 >>= fun e1res -> eval_eexpr st e2 >>= fun e2res ->Printf.printf "%d %d\n" (fst e1res) (fst e2res); OK (eval_binop bop (fst e1res) (fst e2res), st)
   |Ecall(str, argl) -> let evaluator acc x = match eval_eexpr (snd acc) x with |OK v -> (fst acc @ (fst v)::[],snd v) |_ -> failwith "evaluation de la liste d'arguments a fail" in let vargs_st = List.fold_left evaluator ([],st) argl in match do_builtin oc (snd vargs_st).mem str (fst vargs_st) with |OK( Some a) -> OK(a, st) |_ -> let f = match find_function ep str with |OK fu -> fu |_-> failwith  str in (match eval_efun oc (snd vargs_st) f str (fst vargs_st) with |OK (Some resul, st) -> OK(resul,st) |_ -> failwith "L'evaluation de la fonction appelée en tant qu'expression n'a soit pas renvoyé de valeur soit eval_efun a foiré")


(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
and eval_einstr oc (st: int state) (ins: instr) :
  (int option * int state) res =
   match ins with
   |Iassign(str,exp) -> eval_eexpr st exp>>= fun intres -> let x=Hashtbl.replace st.env str (fst intres) in OK(None,st)
   |Iif(exp,ins1,ins2) -> eval_eexpr st exp >>= fun ifres -> Printf.printf "%d\n" (fst ifres);(match (fst ifres) with |0 -> eval_einstr oc st ins2 |_ -> eval_einstr oc st ins1)
   |Iwhile(exp, ins1) ->Printf.printf "oupsi\n"; eval_eexpr st exp >>= fun whileres -> (match (fst whileres) with |0 ->OK(None, st) |_-> eval_einstr oc st (Iblock(ins1::ins::[])))
(*   |Iblock(instrl) -> List.fold_left (fun acc elt -> (match acc with |OK (intopt,st1) ->  eval_einstr oc st1 elt|_ -> failwith "oulah, tu vas t'amuser a debugger ca")) (OK(None,st)) instrl *)
   |Iblock([]) -> OK(None,st)
   |Iblock(ins1::rinstr) -> eval_einstr oc st ins1 >>= fun insres1 -> (match fst insres1 with |None -> eval_einstr oc (snd insres1) (Iblock(rinstr))|Some ret -> OK insres1 )
   |Ireturn(exp) -> eval_eexpr st exp >>= fun expres -> OK(Some (fst expres), st) 
   |Icall(str,expl) -> let evaluator acc x = match eval_eexpr (snd acc) x with |OK v -> (fst acc @ (fst v)::[],snd v) |_ -> failwith "evaluation de la list d'arguments a fail" in let vargs_st = List.fold_left evaluator([],st) expl in match do_builtin oc (snd vargs_st).mem str (fst vargs_st) with |OK (Some a) -> OK(Some a,snd vargs_st) |OK(None) -> OK(None, snd vargs_st) |_ -> let f = match find_function ep str with |OK fu -> fu |_ -> failwith str in (match eval_efun oc (snd vargs_st) f str (fst vargs_st) with |OK (Some resul, st) -> OK(None,st) |_ -> failwith "L'eval de la fonction appelée en tant qu'instruction a foiré")
(*   |Icall(str, expl) -> eval_eexpr st (Ecall(str,expl)) >>= fun callres -> OK(None, snd callres) *)
(*   |Iprint(exp) -> OK(None,st) *)


(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
and eval_efun oc (st: int state) ({ funargs; funbody}: efun)
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
        in
  let st = init_state memsize in
  find_function ep "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length f.funargs in
  let params = take n params in
  eval_efun oc st f "main" params >>= fun (v, st) ->
  match v with
  |Some a -> OK v
  |None -> Error "your prog is useless, dude"
