open Prog
open Elang
open Elang_run
open Batteries
open BatList
open Cfg
open Utils
open Builtins


let eval_cfgprog oc cp memsize params =

let rec eval_cfgexpr st (e: expr) : (int*int state) res =
  match e with
  | Ebinop(b, e1, e2) ->
    eval_cfgexpr st e1 >>= fun v1 ->
    eval_cfgexpr st e2 >>= fun v2 ->
    let v = eval_binop b (fst v1) (fst v2) in
    OK (v,st)
  | Eunop(u, e) ->
    eval_cfgexpr st e >>= fun v1 ->
    let v = (eval_unop u (fst v1)) in
    OK (v,st)
  | Eint i -> OK (i,st)
  | Evar s ->
    begin match Hashtbl.find_option st.env s with
      | Some v -> OK (v,st)
      | None -> Error (Printf.sprintf "Unknown variable %s\n" s)
    end
  | Ecall(str,argl) -> let evaluator acc x = match eval_cfgexpr (snd acc) x with |OK v -> (fst acc @ (fst v)::[],snd v) |_ -> failwith "evaluation de la liste d'arguments a fail" in let vargs_st = List.fold_left evaluator ([],st) argl  in let f = match find_function cp str with |OK fu -> fu |_-> failwith "Error en cherchant une fonction called" in (match eval_cfgfun oc (snd vargs_st) str f (fst vargs_st) with |OK (Some resul, st) -> OK(resul,st) |_ -> failwith "L'evaluation de la fonction appelée en tant qu'expression n'a soit pas renvoyé de valeur soit eval_efun a foiré")
 

and eval_cfginstr oc st ht (n: int): (int * int state) res =
  match Hashtbl.find_option ht n with
  | None -> Error (Printf.sprintf "Invalid node identifier\n")
  | Some node ->
    match node with
    | Cnop succ ->
      eval_cfginstr oc st ht succ
    | Cassign(v, e, succ) ->
      eval_cfgexpr st e >>= fun i ->
      Hashtbl.replace st.env v (fst i);
      eval_cfginstr oc st ht succ
    | Ccmp(cond, i1, i2) ->
      eval_cfgexpr st cond >>= fun i ->
      if (fst i) = 0 then eval_cfginstr oc st ht i2 else eval_cfginstr oc st ht i1
    | Creturn(e) ->
      eval_cfgexpr st e >>= fun e ->
      OK ((fst e), st)
    | Cprint(e, succ) ->
      eval_cfgexpr st e >>= fun e ->
      Format.fprintf oc "%d\n" (fst e);
      eval_cfginstr oc st ht succ
    | Ccall(str, argl, succ) -> eval_cfgexpr st (Ecall(str,argl)) >>= fun callres -> eval_cfginstr oc st ht succ

and eval_cfgfun oc st cfgfunname { cfgfunargs;
                                      cfgfunbody;
                                      cfgentry} vargs =
  let st' = { st with env = Hashtbl.create 17 } in
  match List.iter2 (fun a v -> Hashtbl.replace st'.env a v) cfgfunargs vargs with
  | () -> eval_cfginstr oc st' cfgfunbody cfgentry >>= fun (v, st') ->
    OK (Some v, {st' with env = st.env})
  | exception Invalid_argument _ ->
    Error (Format.sprintf "CFG: Called function %s with %d arguments, expected %d.\n"
             cfgfunname (List.length vargs) (List.length cfgfunargs)
          )

in
  let st = init_state memsize in
  find_function cp "main" >>= fun f ->
  let n = List.length f.cfgfunargs in
  let params = take n params in
  eval_cfgfun oc st "main" f params >>= fun (v, st) ->
  OK v


