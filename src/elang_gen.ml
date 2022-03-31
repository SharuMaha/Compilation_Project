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

let rec compat_type (ty1 : typ) (ty2 : typ) : bool =
        if ((ty1 = Tint && ty2 = Tint) || (ty1 = Tint && ty2 = Tchar) || (ty1 = Tchar && ty2 = Tint) || (ty1 = Tvoid && ty2 = Tvoid) ||(ty1 = Tchar && ty2 = Tchar) ) then true else
               match (ty1,ty2) with
               |(Tptr(ty11),Tptr(ty12)) -> compat_type ty11 ty12
               |(_,_) -> failwith (string_of_typ ty2)




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
        (match (t1,t2) with 
        | (Tptr(_), Tptr(_)) -> failwith "work in progress pour arithmetique entre deux pointeurs, va falloir attendre"
        | (Tint, Tptr(_))
        | (Tchar, Tptr(_)) ->  if (bp = Eadd) then t2 else failwith "tu fais nimp avec les pointeurs coco" 
        | (Tptr(_),Tchar)
        | (Tptr(_), Tint) -> if (bp = Eadd || bp = Esub) then t1 else failwith "tu fais pire que nimp avec les pointeurs"
        | (_, _) ->
        (match (compat_type t1 t2) with 
                |true -> t1
                |false -> failwith "Les deux expr du binop n'ont pas le meme type"))
        |Ecall(str,exprl) -> (match Hashtbl.find_option typ_fun str with
                                |Some t -> (snd t)
                                |None -> failwith "La fonction evaluée dans l'expression n'a pas encore de type défini")
        |Eaddrof(e) -> Tptr( type_expr typ_var typ_fun e)
        |Eload(e) -> type_expr typ_var typ_fun e

let rec addr_taken_expr(e:expr) = 
        match e with
        | Ebinop(b,e1,e2) -> Set.union (addr_taken_expr e1) (addr_taken_expr e2)
        | Eunop (u, e) -> addr_taken_expr e
        | Eint (i) -> Set.empty
        | Evar (s) -> Set.empty
        | Ecall (s, exprl) -> List.fold (fun acc x -> Set.union (addr_taken_expr x) acc) Set.empty exprl
        | Echar (c) -> Set.empty
        | Eaddrof (e) -> match e with |Evar s -> Set.singleton s | _ -> addr_taken_expr e
        | Eload (e) -> addr_taken_expr e

let rec addr_taken_instr(i:instr) = 
        match i with
          | Iassign(s, e) -> addr_taken_expr e
          | Iif (e,i1,i2) -> Set.union (addr_taken_expr e) (Set.union (addr_taken_instr i1) (addr_taken_instr i2))
          | Iwhile (e,i) -> Set.union (addr_taken_expr e) (addr_taken_instr i)
          | Iblock (instrl) -> List.fold (fun acc x -> Set.union (addr_taken_instr x) acc) Set.empty instrl
          | Ireturn (e) -> addr_taken_expr e
          | Icall(s, exprl) -> List.fold (fun acc x -> Set.union (addr_taken_expr x) acc) Set.empty exprl
          | Iinit (s1,s2) -> Set.empty
          | Istore (e1,e2) -> addr_taken_expr e2


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
    
    |Node(Tid, Node(Taddr,[])::StringLeaf(z)::[]) -> let x = type_expr typ_var typ_fun (Evar(z)) in OK(Eaddrof(Evar(z)))

    | _ -> failwith "Unacceptable ast in make_eexpr_of_ast %s"
                    (string_of_ast a)
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg)


let rec imbricounter imbric =
        match imbric with
        |[] -> 1
        |[Node(Tval,imbric2)] -> 1+ imbricounter imbric2
        |_ -> failwith "probleme comptage imbrications"


let rec deref_typ (t1 :typ) (c : int) =
        match (c,t1) with
        |(1, (Tptr(t))) -> t
        |(c1, (Tptr(t))) -> deref_typ t (c1-1)

let rec make_super_deref (s : string) (c : int) = 
        match c with
        |1 -> Eload(Evar(s))
        |c1 -> let x = make_super_deref s (c1-1) in Eload(x)

let rec ref_typ (t1 : typ) (c:int) =
        match c with
        |1 -> Tptr(t1)
        |c1 -> ref_typ (Tptr(t1)) (c1-1)


let rec make_einstr_of_ast (a: tree) (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) : instr res =
  let res =
    match a with
    |Node(Tinit,[Node(Ttype,[StringLeaf(t)]);StringLeaf(a)]) ->if (t <> "void") then Hashtbl.replace typ_var a (typ_of_string t) else failwith "declaration avec void interdite";OK(Iinit(typ_of_string t,a))
    |Node(Tinit,Node(Ttype,Node(Tval,imbric)::StringLeaf(t)::[])::StringLeaf(a)::[]) -> if (t <> "void") then let realt = ref_typ (typ_of_string t) (imbricounter imbric) in Hashtbl.replace typ_var a realt;OK(Iinit(realt,a)) else failwith "declaration void interdite"
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
    |Node(Tassignvar,Node(Tval,imbric)::StringLeaf(a)::exp::[]) -> make_eexpr_of_ast exp typ_var typ_fun >>= fun expres -> let superexpr = make_super_deref a (imbricounter imbric) in if (compat_type ( deref_typ (type_expr typ_var typ_fun (Evar(a))) (imbricounter imbric) ) (type_expr typ_var typ_fun expres)) then (match superexpr with |Eload(ered) -> OK(Istore(ered, expres)) ) else failwith "chepas mais ca marche pô"

    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : (string *typ) res =
  match a with
  | Node (Targ, [Node(Ttype,[Node(Tval,imbric);StringLeaf(t)]);s]) -> OK(string_of_stringleaf s, ptrtyp_of_string (typ_of_string t) imbric)  
  | Node (Targ, [Node(Ttype,[StringLeaf(t)]);s]) ->
    OK (string_of_stringleaf s, typ_of_string t)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))


let make_fundef_of_ast (a: tree) (typ_fun : (string, typ list * typ) Hashtbl.t) : (string * efun) res  =
  match a with
  | Node (Tfundef, [Node(Ttype,[StringLeaf(t)]);StringLeaf fname; Node (Tfunargs, fargs); NullLeaf]) -> let typ_var = Hashtbl.create 20 in list_map_res make_ident fargs >>= fun fargs ->let fargs_typ = List.map( fun x -> snd x) fargs in Hashtbl.replace typ_fun fname (fargs_typ,(typ_of_string t));List.iter(fun (str,typ)-> Hashtbl.replace typ_var str typ) fargs ; OK("", {funargs = []; funbody = Iinit(Tint,"fk2") ; funvartyp = (Hashtbl.create 10) ; funrettype = Tint;funvarinmem = Hashtbl.create 10; funstksz = 0})
  | Node (Tfundef, [Node(Ttype,[StringLeaf(t)]);StringLeaf fname; Node (Tfunargs, fargs); fbody]) ->
                  let typ_var = Hashtbl.create 20 in list_map_res make_ident fargs >>= fun fargs ->let fargs_typ = List.map( fun x -> snd x) fargs in Hashtbl.replace typ_fun fname (fargs_typ,(typ_of_string t));List.iter(fun (str,typ)-> Hashtbl.replace typ_var str typ) fargs ;make_einstr_of_ast fbody typ_var typ_fun >>= fun fbodyres -> let varsinstack = addr_taken_instr fbodyres in let funvarinmem = Hashtbl.create 10 in let funstksz = Set.fold (fun x acc  -> Hashtbl.replace funvarinmem x acc;match size_type(Hashtbl.find typ_var x) with |OK sz -> sz+acc |_ -> failwith "problem" ) varsinstack 0 in OK (fname, {funargs = fargs; funbody = fbodyres; funvartyp = typ_var;funrettype = (typ_of_string t); funvarinmem = funvarinmem; funstksz = funstksz })
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
  list_map_res (fun a -> make_fundef_of_ast a typ_fun >>= fun (fname,  efun) -> OK (fname, Gfun efun)) l >>= fun list_avec_fake -> OK(List.filter(fun x -> fst x <> "") list_avec_fake)
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

