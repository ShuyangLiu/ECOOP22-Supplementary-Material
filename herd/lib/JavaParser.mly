%{
open JavaBase
open JavaType
open Misc
%}

%token EOF
%token <string> IDENTIFIER
%token <string> VARHANDLE
%token <int> PROC
%token LPAR RPAR COMMA LBRACE RBRACE
%token INT DOUBLE

%token <int> CONSTANT
%token NULL
%token SEMI COLON EQ EQ_OP NEQ_OP LT LE GT GE DOT
%token XOR OR
%token AND
%token ADD SUB
%token MUL DIV
%token WHILE IF ELSE
%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE
%token <AccessModes.t> WRITE
%token <AccessModes.t> READ
%token <AccessModes.t * AccessModes.t> COMPARE_AND_EXCHANGE
%token <JavaBase.rmw> GET_AND_OP
%token FENCE_FULL FENCE_ACQUIRE FENCE_RELEASE FENCE_LL FENCE_SS

%left OR
%left XOR
%left AND

%nonassoc EQ_OP NEQ_OP LT LE GT GE
%left ADD SUB
%left MUL DIV

%type <JavaAst.thread_body list> main
%start main

%%

fence :
| FENCE_FULL    { Fence (MemOrderOrAnnot.AM AccessModes.Volatile) }
| FENCE_ACQUIRE { Fence (MemOrderOrAnnot.AM AccessModes.Acquire)  }
| FENCE_RELEASE { Fence (MemOrderOrAnnot.AM AccessModes.Release)  }
| FENCE_LL      { Fence (MemOrderOrAnnot.AM AccessModes.Acquire)  }
| FENCE_SS      { Fence (MemOrderOrAnnot.AM AccessModes.Release)  }
;

expr:
| LPAR expr RPAR { $2 }
| CONSTANT { Const $1 }
| IDENTIFIER { LoadReg $1 }
| VARHANDLE DOT READ LPAR RPAR { LoadMem ($1, $3) }
| VARHANDLE DOT COMPARE_AND_EXCHANGE LPAR expr COMMA expr RPAR { CAS ($1, $3, $5, $7) }
| VARHANDLE DOT GET_AND_OP LPAR expr RPAR { Rmw ($1, $3, $5) }
| expr MUL expr { Op(Op.Mul, $1, $3) }
| expr ADD expr { Op(Op.Add, $1, $3) }
| expr SUB expr { Op(Op.Sub, $1, $3) }
| expr DIV expr { Op(Op.Div, $1, $3) }
| expr AND expr { Op(Op.And, $1, $3) }
| expr OR expr  { Op(Op.Or, $1, $3)  }
| expr XOR expr { Op(Op.Xor, $1, $3) }
| expr EQ_OP expr  { Op(Op.Eq, $1, $3) }
| expr NEQ_OP expr { Op(Op.Ne, $1, $3) }
| expr LT expr { Op(Op.Lt, $1, $3) }
| expr GT expr { Op(Op.Gt, $1, $3) }
| expr LE expr { Op(Op.Le, $1, $3) }
| expr GE expr { Op(Op.Ge, $1, $3) }
;

initialisation:
| typ IDENTIFIER EQ expr { StoreReg ($2, $4) }
;

instruction:
| IF LPAR expr RPAR block_ins %prec LOWER_THAN_ELSE
  { If($3, $5, None) }
| IF LPAR expr RPAR block_ins ELSE block_ins
  { If($3, $5, Some $7) }
| initialisation SEMI
  { $1 }
| IDENTIFIER EQ expr SEMI
  { StoreReg($1, $3) }
| VARHANDLE DOT WRITE LPAR expr RPAR SEMI
  { StoreMem($1, $3, $5) }
| fence LPAR RPAR SEMI
  { $1 }
;

typ:
| INT    { JavaType.Int    }
| DOUBLE { JavaType.Double }
;

declaration:
| typ IDENTIFIER SEMI { DeclReg ($2) }
;

ins_seq:
| block_ins { [$1] }
| block_ins ins_seq { $1::$2 }
| declaration { [] }
| declaration ins_seq { $2 }
;

block_ins:
| instruction { $1 }
| LBRACE ins_seq RBRACE { Seq($2) }
;

pseudo_seq:
| block_ins { [Instruction $1] }
| block_ins pseudo_seq { (Instruction $1)::$2 }
| declaration { [] }
| declaration pseudo_seq { $2 }
;

function_def :
| PROC LBRACE pseudo_seq RBRACE
  { { JavaAst.proc = $1;
      JavaAst.body = $3 } }
;

trans_unit :
| { [] }
| function_def trans_unit { $1 :: $2 }
;

main :
| trans_unit EOF { $1 }
;
