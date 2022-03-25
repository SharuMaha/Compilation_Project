open Batteries
open Elang
open Prog
open Utils


let dump_binop = function
  | Eadd -> Printf.sprintf "+"
  | Esub -> Printf.sprintf "-"
  | Emul -> Printf.sprintf "*"
  | Ediv -> Printf.sprintf "/"
  | Emod -> Printf.sprintf "%%"
  | Exor -> Printf.sprintf "^"
  | Eclt -> Printf.sprintf "<"
  | Ecle -> Printf.sprintf "<="
  | Ecgt -> Printf.sprintf ">"
  | Ecge -> Printf.sprintf ">="
  | Eceq -> Printf.sprintf "=="
  | Ecne -> Printf.sprintf "!="

let dump_unop = function
  | Eneg -> Printf.sprintf "-"

let rec dump_eexpr = function
  | Ebinop(b, e1, e2) -> Printf.sprintf "(%s %s %s)" (dump_eexpr e1) (dump_binop b) (dump_eexpr e2)
  | Eunop(u, e) -> Printf.sprintf "(%s %s)" (dump_unop u) (dump_eexpr e)
  | Eint i -> Printf.sprintf "%d" i
  | Evar s -> Printf.sprintf "%s" s
  | Echar c -> Printf.sprintf "%c" c
  | Ecall(str,argl) -> Printf.sprintf "%s(%s)" str (String.concat "," (List.map (fun x -> dump_eexpr x) argl))

let indent_size = 2
let spaces n =
  range (indent_size*n) |> List.map (fun _ -> ' ') |> String.of_list

let print_spaces oc n =
  Format.fprintf oc "%s" (spaces n)

let rec dump_einstr_rec indent oc i =
  match i with
  | Iassign(v, e) ->
    print_spaces oc indent;
    Format.fprintf oc "%s = %s;\n" v (dump_eexpr e)
  | Iif(cond, i1, i2) ->
    print_spaces oc indent;
    Format.fprintf oc "if (%s) %a else %a\n"
                           (dump_eexpr cond) (dump_einstr_rec (indent)) i1 (dump_einstr_rec (indent)) i2
  | Iwhile(cond, i) ->
    print_spaces oc indent;
    Format.fprintf oc "while (%s) %a\n"
                         (dump_eexpr cond) (dump_einstr_rec (indent)) i
  | Iblock(il) ->
    Format.fprintf oc "{\n";
    List.iter (Format.fprintf oc "%a" (dump_einstr_rec (indent + 1))) il;
    print_spaces oc indent;
    Format.fprintf oc "}";
  | Ireturn(e) ->
    print_spaces oc indent;
    Format.fprintf oc "return %s;\n" (dump_eexpr e)
  | Icall(str,argl) ->
    print_spaces oc indent;
    Format.fprintf oc "%s(%s)\n" str (String.concat "," (List.map (fun x -> dump_eexpr x) argl))

  | Iinit(typ,str) ->
    print_spaces oc indent;
    Format.fprintf oc "%s %s;\n" typ str

let dump_einstr oc i = dump_einstr_rec 0 oc i


let dump_efun oc funname {funargs; funbody} =
  let fargs_wtyp = List.map (fun (str,typ) -> let str_space =  String.cat (string_of_typ typ) " " in String.cat str_space str) funargs in
  Format.fprintf oc "%s(%s) %a"
    funname
    (String.concat "," fargs_wtyp)
    dump_einstr funbody

let dump_eprog oc = dump_prog dump_efun oc

let dump_e oc p =
  dump_eprog oc p
