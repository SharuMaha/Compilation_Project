tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int> SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD SYM_CHARACTER<char>
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA 
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ
tokens SYM_VOID SYM_INT SYM_CHAR
non-terminals S INSTR INSTRS BLOC ELSE EXPR FACTOR
non-terminals LPARAMS REST_PARAMS
non-terminals IDENTIFIER INTEGER
non-terminals FUNDEF FUNDEFS
non-terminals ADD_EXPRS ADD_EXPR
non-terminals MUL_EXPRS MUL_EXPR
non-terminals CMP_EXPRS CMP_EXPR
non-terminals EQ_EXPRS EQ_EXPR
non-terminals LCALLPARAMS CALLREST_PARAMS
non-terminals ASSIGN_OR_CALL NOTHING_OR_CALL JUST_ASSIGN
non-terminals TYPE
axiom S
{

  open Symbols
  open Ast
  open BatPrintf
  open BatBuffer
  open Batteries
  open Utils

  type call_me_maybe =
	| CallMe of tree
	| Dont_and_assign of tree
	| Dont_and_init
	

  let rec resolve_associativity (term : Ast.tree) other : Ast.tree =
       	match other with
	|[] -> term
	|(tag, next_tree)::r -> resolve_associativity (Node (tag, [term; next_tree])) r

}

rules
S -> FUNDEFS SYM_EOF {  Node (Tlistglobdef, $1) }
FUNDEFS -> FUNDEF FUNDEFS {Node(Tfundef,$1)::$2}
FUNDEFS -> {[]}
FUNDEF -> TYPE SYM_IDENTIFIER SYM_LPARENTHESIS LPARAMS SYM_RPARENTHESIS BLOC { StringLeaf($2)::Node(Tfunargs, $4)::$6::[] }
LPARAMS -> TYPE SYM_IDENTIFIER REST_PARAMS { Node(Targ, [StringLeaf($2)]) :: $3 }
LPARAMS -> {[]}
REST_PARAMS -> SYM_COMMA TYPE SYM_IDENTIFIER REST_PARAMS { Node(Targ, [StringLeaf($3)]) :: $4 }
REST_PARAMS -> {[]}

TYPE -> SYM_VOID {"void"}
TYPE -> SYM_INT {"int"}
TYPE -> SYM_CHAR {"char"}


LCALLPARAMS -> EXPR CALLREST_PARAMS { $1::$2 }
LCALLPARAMS -> {[]}
CALLREST_PARAMS -> SYM_COMMA EXPR CALLREST_PARAMS { $2::$3 }
CALLREST_PARAMS -> {[]}



INSTR -> TYPE SYM_IDENTIFIER ASSIGN_OR_CALL {match $3 with |CallMe(t1) -> Node(Tcall, StringLeaf($2)::t1::[]) |Dont_and_assign(t2) -> Node(Tassign, [Node(Tassignvar, Node(Ttype,[StringLeaf($1)])::StringLeaf($2)::[t2])]) |Dont_and_init -> Node(Tinit,[Node(Ttype, [StringLeaf($2)])]) }

INSTR -> SYM_IDENTIFIER ASSIGN_OR_CALL {match $2 with |CallMe(t1) -> Node(Tcall, StringLeaf($1)::t1::[]) |Dont(t2) -> Node(Tassign, [Node(Tassignvar, StringLeaf($1)::[t2])]) }

ASSIGN_OR_CALL -> SYM_ASSIGN EXPR SYM_SEMICOLON {Dont_and_assign($2)}
ASSIGN_OR_CALL -> SYM_SEMICOLON {Dont_and_init}

ASSIGN_OR_CALL -> SYM_LPARENTHESIS LCALLPARAMS SYM_RPARENTHESIS SYM_SEMICOLON { CallMe(Node(Targs, $2))}

INSTR -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS BLOC ELSE {Node(Tif, $3::$5::$6)}
INSTR -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS INSTR {Node(Twhile, $3::$5::[])}
INSTR -> SYM_RETURN EXPR SYM_SEMICOLON {Node(Treturn, [$2])}
INSTR -> BLOC {$1}

EXPR -> EQ_EXPR EQ_EXPRS {resolve_associativity $1 $2}
EQ_EXPR -> CMP_EXPR CMP_EXPRS {resolve_associativity $1 $2}
CMP_EXPR -> ADD_EXPR ADD_EXPRS {resolve_associativity $1 $2}
ADD_EXPR -> MUL_EXPR MUL_EXPRS {resolve_associativity $1 $2}
MUL_EXPR -> FACTOR {$1}
MUL_EXPR -> SYM_MINUS FACTOR {Node(Tneg, [$2])}
FACTOR -> SYM_INTEGER {IntLeaf($1)}
FACTOR -> SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS {$2}
FACTOR -> SYM_CHARACTER {CharLeaf($1)}

FACTOR -> SYM_IDENTIFIER NOTHING_OR_CALL {match $2 with |Dont_and_assign(t1) -> StringLeaf($1) |CallMe(t2) -> Node(Tcall, StringLeaf($1)::t2::[])}
NOTHING_OR_CALL -> {Dont_and_assign(NullLeaf)}
NOTHING_OR_CALL -> SYM_LPARENTHESIS LCALLPARAMS SYM_RPARENTHESIS {CallMe(Node(Targs, $2))}


MUL_EXPRS -> SYM_ASTERISK MUL_EXPR MUL_EXPRS {(Tmul, $2):: $3}
MUL_EXPRS -> SYM_DIV MUL_EXPR MUL_EXPRS {(Tdiv, $2)::$3}
MUL_EXPRS -> SYM_MOD MUL_EXPR MUL_EXPRS {(Tmod, $2)::$3}
MUL_EXPRS -> {[]}
ADD_EXPRS -> SYM_PLUS ADD_EXPR ADD_EXPRS {(Tadd, $2):: $3}
ADD_EXPRS -> SYM_MINUS ADD_EXPR ADD_EXPRS {(Tsub, $2)::$3}
ADD_EXPRS -> {[]}

EQ_EXPRS -> SYM_EQUALITY EQ_EXPR EQ_EXPRS {(Tceq, $2):: $3}
EQ_EXPRS -> {[]}

CMP_EXPRS -> SYM_NOTEQ CMP_EXPR CMP_EXPRS {(Tne, $2)::$3}
CMP_EXPRS -> SYM_LT CMP_EXPR CMP_EXPRS {(Tclt, $2)::$3}
CMP_EXPRS -> SYM_LEQ CMP_EXPR CMP_EXPRS {(Tcle, $2):: $3}
CMP_EXPRS -> SYM_GT CMP_EXPR CMP_EXPRS {(Tcgt, $2):: $3}
CMP_EXPRS -> SYM_GEQ CMP_EXPR CMP_EXPRS {(Tcge, $2)::$3}
CMP_EXPRS -> {[]}

ELSE -> SYM_ELSE BLOC {$2::[]}
ELSE -> {[]}
INSTRS -> INSTR INSTRS {$1 :: $2}
INSTRS -> {[]}
BLOC -> SYM_LBRACE INSTRS SYM_RBRACE {Node(Tblock,$2)}
IDENTIFIER -> SYM_IDENTIFIER {[]}
INTEGER -> SYM_INTEGER {[]}
 
