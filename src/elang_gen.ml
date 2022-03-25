open Ast
open Elang
open Prog
open Report
open Options
open Batteries
open Elang_print
open Utils

let tag_is_binop =
  function
    Tadd -> true
  | Tsub -> true
  | Tmul -> true
  | Tdiv -> true
  | Tmod -> true
  | Txor -> true
  | Tcle -> true
  | Tclt -> true
  | Tcge -> true
  | Tcgt -> true
  | Tceq -> true
  | Tne  -> true
  | _    -> false

let binop_of_tag =
  function
    Tadd -> Eadd
  | Tsub -> Esub
  | Tmul -> Emul
  | Tdiv -> Ediv
  | Tmod -> Emod
  | Txor -> Exor
  | Tcle -> Ecle
  | Tclt -> Eclt
  | Tcge -> Ecge
  | Tcgt -> Ecgt
  | Tceq -> Eceq
  | Tne -> Ecne
  | _ -> assert false

let compat_type (ty1 : typ) (ty2 : typ) : bool =
        if ((ty1 = Tint && ty2 = Tint) || (ty1 = Tint && ty2 = Tchar) || (ty1 = Tchar && ty2 = Tint) || (ty1 = Tvoid && ty2 = Tvoid) ||(ty1 = Tchar && ty2 = Tchar) ) then true else failwith (string_of_typ ty2)

(* Func qui compute le type d'une expression*)
let rec type_expr (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (e:expr) : typ =
        match e with
        |Echar(c) -> Tchar
        |Eint(i) -> Tint
        |Evar(s) -> (match Hashtbl.find_option typ_var s with
                        |Some t -> t
                        |None -> failwith "Cette variable n'a pas encore de type défini")
        |Eunop(u, exp) -> type_expr typ_var typ_fun exp
        |Ebinop(bp, exp1, exp2) -> let t1 = type_expr typ_var typ_fun exp1 in let t2 = type_expr typ_var typ_fun exp2 in 
        (match (compat_type t1 t2) with 
                |true -> t1
                |false -> failwith "Les deux expr du binop n'ont pas le meme type")
        |Ecall(str,exprl) -> (match Hashtbl.find_option typ_fun str with
                                |Some t -> (snd t)
                                |None -> failwith "La fonction evaluée dans l'expression n'a pas encore de type défini")



(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)



let rec make_eexpr_of_ast (a: tree) (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) : expr res =
  let res =
    match a with
    | Node(t, [e1; e2]) when tag_is_binop t -> make_eexpr_of_ast e1 typ_var typ_fun >>= fun e1res -> make_eexpr_of_ast e2 typ_var typ_fun >>= fun e2res ->
                    let x= type_expr typ_var typ_fun (Ebinop(binop_of_tag t,e1res ,e2res)) in OK(Ebinop(binop_of_tag t,e1res ,e2res))
    | Node (Tneg,[e1]) -> make_eexpr_of_ast e1 typ_var typ_fun >>= fun e1res -> let x= type_expr typ_var typ_fun (Eunop(Eneg, e1res)) in OK(Eunop(Eneg, e1res))
    | StringLeaf(a) -> let x = type_expr typ_var typ_fun (Evar(a)) in OK(Evar(a))
    | IntLeaf(a) -> let x = type_expr typ_var typ_fun (Eint(a)) in OK(Eint(a))
    | CharLeaf(c) -> let x = type_expr typ_var typ_fun (Echar(c)) in OK(Echar(c))
    | Node(Tcall,[StringLeaf(f);Node(Targs, argl)]) -> let get_expr x = match (make_eexpr_of_ast x typ_var typ_fun) with |OK v -> v |_ -> failwith "oops error with args of call"
                        in let x = type_expr typ_var typ_fun (Ecall(f,List.map get_expr argl)) in let exprl = List.map get_expr argl in let typ_exprl = List.map (type_expr typ_var typ_fun) exprl in let sign_arg = (fst (Hashtbl.find typ_fun f)) in if (typ_exprl= sign_arg) then  OK(Ecall(f,exprl)) else failwith "Appel à fonction avec des arguments du mauvais type"
    | _ -> failwith "Unacceptable ast in make_eexpr_of_ast %s"
                    (string_of_ast a)
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg)
let rec make_einstr_of_ast (a: tree) (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) : instr res =
  let res =
    match a with
    |Node(Tinit,[Node(Ttype,[StringLeaf(t)]);StringLeaf(a)]) ->if (t <> "void") then Hashtbl.replace typ_var a (typ_of_string t) else failwith "declaration avec void interdite";OK(Iinit(t,a))
    |Node(Tassign, [e1]) -> make_einstr_of_ast e1 typ_var typ_fun
    |Node(Tassignvar,StringLeaf(a)::exp::[]) -> make_eexpr_of_ast exp typ_var typ_fun >>= fun expres -> if (compat_type (type_expr typ_var typ_fun (Evar(a))) (type_expr typ_var typ_fun expres)) then OK(Iassign(a,expres)) else Error "Assignation avec types pas compatibles"
    |Node(Twhile, [e1;e2]) -> make_eexpr_of_ast e1 typ_var typ_fun >>= fun e1res -> make_einstr_of_ast e2 typ_var typ_fun >>= fun e2res -> OK(Iwhile(e1res,e2res))
    |Node(Tblock,linstr) ->let get_instr x = match (make_einstr_of_ast x typ_var typ_fun) with |OK v -> v |_ -> failwith "Erreur avec une instr du block"
                           in  OK(Iblock(List.map get_instr linstr))
    |Node(Treturn, [e]) ->make_eexpr_of_ast e typ_var typ_fun >>= fun eres -> OK(Ireturn(eres))

    |Node(Tif, cond::prem::[]) -> make_eexpr_of_ast cond typ_var typ_fun>>= fun condres -> make_einstr_of_ast prem typ_var typ_fun >>= fun premres -> OK(Iif(condres,premres,Iblock([])))
    |Node(Tif, cond::prem::sec::[]) ->make_eexpr_of_ast cond  typ_var typ_fun>>= fun condres -> make_einstr_of_ast prem typ_var typ_fun >>= fun premres -> make_einstr_of_ast sec typ_var typ_fun >>= fun secres -> OK(Iif(condres, premres, secres))

    |Node(Tcall,[StringLeaf(f);Node(Targs, argl)]) -> let get_expr x = match (make_eexpr_of_ast x typ_var typ_fun) with |OK v -> v |_ -> failwith "oops error with args of call"
                                      in let exprl = List.map get_expr argl in let typ_exprl = List.map (type_expr typ_var typ_fun) exprl in let sign_arg = (fst (Hashtbl.find typ_fun f)) in if (typ_exprl= sign_arg) then  OK(Icall(f,exprl)) else failwith "Appel à fonction avec des arguments du mauvais type"


    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : (string *typ) res =
  match a with
  | Node (Targ, [Node(Ttype,[StringLeaf(t)]);s]) ->
    OK (string_of_stringleaf s, typ_of_string t)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_fundef_of_ast (a: tree) (typ_fun : (string, typ list * typ) Hashtbl.t) : (string * efun) option res  =
  match a with
  | Node (Tfundef, [Node(Ttype,[StringLeaf(t)]);StringLeaf fname; Node (Tfunargs, fargs); NullLeaf]) -> let typ_var = Hashtbl.create 20 in list_map_res make_ident fargs >>= fun fargs ->let fargs_typ = List.map( fun x -> snd x) fargs in Hashtbl.replace typ_fun fname (fargs_typ,(typ_of_string t));List.iter(fun (str,typ)-> Hashtbl.replace typ_var str typ) fargs ;OK(None)
  | Node (Tfundef, [Node(Ttype,[StringLeaf(t)]);StringLeaf fname; Node (Tfunargs, fargs); fbody]) ->
                  let typ_var = Hashtbl.create 20 in list_map_res make_ident fargs >>= fun fargs ->let fargs_typ = List.map( fun x -> snd x) fargs in Hashtbl.replace typ_fun fname (fargs_typ,(typ_of_string t));List.iter(fun (str,typ)-> Hashtbl.replace typ_var str typ) fargs ;make_einstr_of_ast fbody typ_var typ_fun >>= fun fbodyres -> OK (Some(fname, {funargs = fargs; funbody = fbodyres; funvartyp = typ_var;funrettype = (typ_of_string t) }))
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a)) 

let make_eprog_of_ast (a: tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
    let typ_fun = Hashtbl.create (List.length l) in
        Hashtbl.replace typ_fun "print" ([Tint], Tvoid);
        Hashtbl.replace typ_fun "print_int" ([Tint], Tvoid);
        Hashtbl.replace typ_fun "print_char" ([Tchar], Tvoid);
    list_map_res (fun a -> make_fundef_of_ast a typ_fun >>= fun (fname,  efun) -> OK (fname, Gfun efun)) l
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tlistglobdef, got %s."
             (string_of_ast a))

let pass_elang ast =
  match make_eprog_of_ast ast with
  | Error msg ->
    record_compile_result ~error:(Some msg) "Elang";
    Error msg
  | OK  ep ->
    dump !e_dump dump_e ep (fun file () ->
        add_to_report "e" "E" (Code (file_contents file))); OK ep

