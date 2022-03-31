open Batteries
open Utils
open Ast

type typ =
  Tint
| Tchar
| Tvoid
| Tptr of typ

let rec string_of_typ t =
match t with
| Tint -> "int"
| Tchar -> "char"
| Tvoid -> "void"
| Tptr(t1) -> String.cat (string_of_typ t1) "*"
let typ_of_string t =
match t with
| "int" -> Tint
| "char" -> Tchar
| "void" -> Tvoid

let rec ptrtyp_of_string t imbric =
        match imbric with
        |[] -> Tptr(t)
        |[Node(Tval, imbric2)] -> ptrtyp_of_string (Tptr(t)) imbric2
        | _ -> failwith "ptrtyp_of_string est fait sur nimp"

type mem_access_size =
  | MAS1
  | MAS4
  | MAS8

let string_of_mem_access_size mas =
  match mas with
  | MAS1 -> "{1}"
  | MAS4 -> "{4}"
  | MAS8 -> "{8}"

let mas_of_size n =
  match n with
  | 1 -> OK MAS1
  | 4 -> OK MAS4
  | 8 -> OK MAS8
  | _ -> Error (Printf.sprintf "Unknown memory access size for size = %d" n)


let size_of_mas mas =
  match mas with
  | MAS1 -> 1
  | MAS4 -> 4
  | MAS8 -> 8

let archi_mas () =
  match !Archi.archi with
  | A64 -> MAS8
  | A32 -> MAS4


let size_type(t:typ) :int res =
        match t with 
        |Tptr (_)
        |Tint -> OK(size_of_mas (archi_mas()))
        |Tchar -> OK(1)
        |_ -> failwith"Sorry je connais pas la taille de ton truc"

type 'a gdef = Gfun of 'a

type 'a prog = (string * 'a gdef) list


let dump_gdef dump_fun oc gd =
  match gd with
  | (fname, Gfun f) ->
    dump_fun oc fname f;
    Format.fprintf oc "\n"

let dump_prog dump_fun oc =
  List.iter (dump_gdef dump_fun oc)

type 'a state = {
  env: (string, 'a) Hashtbl.t;
  mem: Mem.t
}

let init_state memsize =
  {
    mem = Mem.init memsize;
    env = Hashtbl.create 17;
  }

let set_val env v i =
  Hashtbl.replace env v i

let get_val env v =
  Hashtbl.find_option env v

let find_function (ep: 'a prog) fname : 'a res =
  match List.assoc_opt fname ep with
  | Some (Gfun f) -> OK f
  | _ -> Error (Format.sprintf "Unknown function %s\n" fname)
