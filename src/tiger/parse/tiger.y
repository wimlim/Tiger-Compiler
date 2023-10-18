%filenames parser
%scanner tiger/lex/scanner.h
%baseclass-preinclude tiger/absyn/absyn.h

 /*
  * Please don't modify the lines above.
  */

%union {
  int ival;
  std::string* sval;
  sym::Symbol *sym;
  absyn::Exp *exp;
  absyn::ExpList *explist;
  absyn::Var *var;
  absyn::DecList *declist;
  absyn::Dec *dec;
  absyn::EFieldList *efieldlist;
  absyn::EField *efield;
  absyn::NameAndTyList *tydeclist;
  absyn::NameAndTy *tydec;
  absyn::FieldList *fieldlist;
  absyn::Field *field;
  absyn::FunDecList *fundeclist;
  absyn::FunDec *fundec;
  absyn::Ty *ty;
  }

%token <sym> ID
%token <sval> STRING
%token <ival> INT

%token
  COMMA COLON SEMICOLON LPAREN RPAREN LBRACK RBRACK
  LBRACE RBRACE DOT
  PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE
  AND OR ASSIGN
  ARRAY IF THEN ELSE WHILE FOR TO DO LET IN END OF
  BREAK NIL
  FUNCTION VAR TYPE

 /* token priority */
 /* TODO: Put your lab3 code here */
%left OR
%left AND
%nonassoc EQ NEQ LT LE GT GE
%left PLUS MINUS
%left TIMES DIVIDE
%left UMINUS

%type <exp> exp expseq
%type <explist> actuals nonemptyactuals sequencing sequencing_exps
%type <var> lvalue one oneormore
%type <declist> decs decs_nonempty
%type <dec> decs_nonempty_s vardec
%type <efieldlist> rec rec_nonempty
%type <efield> rec_one
%type <tydeclist> tydec
%type <tydec> tydec_one
%type <fieldlist> tyfields tyfields_nonempty
%type <field> tyfield
%type <ty> ty
%type <fundeclist> fundec
%type <fundec> fundec_one

%start program

%%
program:  exp  {absyn_tree_ = std::make_unique<absyn::AbsynTree>($1);};

exp: lvalue               {$$ = new absyn::VarExp(scanner_.GetTokPos)(), $1);}
  |  INT                  {$$ = new absyn::IntExp(scanner_.GetTokPos(), $1);}
  |  STRING               {$$ = new absyn::StringExp(scanner_.GetTokPos(), $1);}
  |  NIL                  {$$ = new absyn::NilExp(scanner_.GetTokPos());}
  |  MINUS exp %prec UMINUS {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::MINUS_OP, new absyn::IntExp(scanner_.GetTokPos(), 0), $2);}
  |  exp PLUS exp {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::PLUS_OP, $1, $3);}
  |  exp MINUS exp        {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::MINUS_OP, $1, $3);}
  |  exp TIMES exp        {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::TIMES_OP, $1, $3);}
  |  exp DIVIDE exp       {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::DIVIDE_OP, $1, $3);}
  |  exp EQ exp           {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::EQ_OP, $1, $3);}
  |  exp NEQ exp          {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::NEQ_OP, $1, $3);}
  |  exp LT exp           {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::LT_OP, $1, $3);}
  |  exp LE exp           {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::LE_OP, $1, $3);}
  |  exp GT exp           {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::GT_OP, $1, $3);}
  |  exp GE exp           {$$ = new absyn::OpExp(scanner_.GetTokPos(), absyn::OpExp::GE_OP, $1, $3);}
  |  exp AND exp          {$$ = new absyn::IfExp(scanner_.GetTokPos(), $1, $3, new absyn::IntExp(scanner_.GetTokPos(), 0));}
  |  exp OR exp           {$$ = new absyn::IfExp(scanner_.GetTokPos(), $1, new absyn::IntExp(scanner_.GetTokPos(), 0), $3);}
  |  IF exp THEN exp      {$$ = new absyn::IfExp(scanner_.GetTokPos(), $2, $4, nullptr);}
  |  IF exp THEN exp else exp {$$ = new absyn::IfExp(scanner_.GetTokPos(), $2, $4, $6);}
  |  WHILE exp DO exp     {$$ = new absyn::WhileExp(scanner_.GetTokPos(), $2, $4);}
  |  FOR ID ASSIGN exp TO exp DO exp {$$ = new absyn::ForExp(scanner_.GetTokPos(), $2, $4, $6, $8);}
  |  BREAK                {$$ = new absyn::BreakExp(scanner_.GetTokPos());}
  |  LET decs IN exp END  {$$ = new absyn::LetExp(scanner_.GetTokPos(), $2, $4);}
  |  ID LBRACE exp RBRACE OF exp {$$ = new absyn::ArrayExp(scanner_.GetTokPos(), $1, $3, $6);}
  |  LPAREN RPAREN        {$$ = new absyn::voidExp(scanner_.GetTokPos());}
  |  LPAREN expseq RPAREN {$$ = $2;}
  |  lvalue ASSIGN exp    {$$ = new absyn::assignExp(scanner_.GetTokPos(), $1, $3);}
  |  ID LPAREN actuals RPAREN {$$ = new absyn::CallExp(scanner.GetTokPos(), $1, $3);}
  |  ID LBRACE rec RBRACE {$$ = new absyn::RecordExp(scanner_.GetTokPos(), $1, $3);}
  |  ID LBRACK exp RBRACK {$$ = new absyn::SubscriptVar(scanner_.GetTokPos(), new absyn::SimpleVar(scanner_.GetTokPos(), $1), $3);}
  ;

lvalue:  ID  {$$ = new absyn::SimpleVar(scanner_.GetTokPos(), $1);}
  |   oneormore   {$$ = $1;}
  ;

one: ID DOT ID {$$ = new absyn::FieldVar(scanner_.GetTokPos(), new absyn::SimpleVar(scanner_.GetTokPos(), $1), $3);)}
  |  ID LBRACK exp RBRACK {$$ = new absyn::SubscriptVar(scanner_.GetTokPos(), new absyn::SimpleVar(scanner_.GetTokPos(), $1), $3);}
  ;

oneormore: one {$$ = $1;}
  |   oneormore DOT ID {$$ = new absyn::FieldVar(scanner_.GetTokPos(), $1, $3);}
  |   oneormore LBRACK exp RBRACK {$$ = new absyn::SubscriptVar(scanner_.GetTokPos(), $1, $3);}
  ;

expseq:       {$$ = new absysn::SeqEXp(scanner_.GetTokPos(), nullptr);}
  |   exp     {$$ = new absyn::SeqExp(scanner_.GetTokPos(), new basyn::ExpList($1));}
  |   explist {$$ = new absyn::SeqExp(scanner_.GetTokPos(), $1);}
  ;

actuals:              {$$ = new absyn::ExpList();}
  |   nonemptyactuals {$$ = $1;}
  ;

nonemptyactuals:  exp           {$$ = new absyn::ExpList($1);}
  |   nonemptyactuals COMMA exp {$$ = new absyn::ExpList($3, $1);}
  ;

sequencing:   LPAREN expseq RPAREN {$$ = $2;}
  |   LPAREN RPAREN {$$ = new absyn::SeqExp(scanner_.GetTokPos(), nullptr);}
  ;

sequencing_exps:  exp SEMICOLON exp {$$ = new absyn::ExpList($3))->Prepend($1);}
  |   exps SEMICOLON sequencing_exps {$$ = $3->Prepend($1);}
  ;

decs:  {$$ = new absyn::DecList();}
  |   decs_nonempty {$$ = $1;}
  ;

decs_nonempty:  decs_nonempty_s {$$ = new basyn::(DecList($1));}
  |   decs_nonempty_s decs_nonempty {$$ = $2->Prepend($1);}
  ;

decs_nonempty_s:  vardec {$$ = $1;}
  |   fundec {$$ = new absyn::TypeDec(scanner_.GetTokPos(), $1);}
  |   tydec {$$ = $1;}
  ;

vardec: var ID COLON ID ASSIGN exp {$$ = new absyn::VarDec(scanner_.GetTokPos(), $2, $4, $6);}
  |   var ID ASSIGN exp {$$ = new absyn::VarDec(scanner_.GetTokPos(), $2, nullptr, $4);}
  ;

rec:  rec_one {$$ = new absyn::EFieldList($1);}
  |   rec_one COMMA rec {$$ = $3->Prepend($1);}
  ;

rec_one: ID EQ exp {$$ = new absyn::EField(scanner_.GetTokPos(), $1, $3);}
  ;

rec_nonempty: rec_one {$$ = new absyn::EFieldList($1);}
  |   rec_one COMMA rec_nonempty {$$ = $3->Prepend($1);}
  ;

tydec: tydec_one {$$ = new absyn::NameAndTyList($1);}
  |   tydec_one tydec {$$ = $2->Prepend($1);}
  ;

tydec_one: TYPE ID EQ ty {$$ = new absyn::TyDec(scanner_.GetTokPos(), $2, $4);}
  ;


ty:   ID {$$ = new absyn::NameTy(scanner_.GetTokPos(), $1);}
  |   LBRACE tyfields RBRACE {$$ = new absyn::RecordTy(scanner_.GetTokPos(), $2);}
  |   ARRAY OF ID {$$ = new absyn::ArrayTy(scanner_.GetTokPos(), $3);}
  ;

tyfields: {$$ = new absyn::FieldList();}
  |   tyfields_nonempty {$$ = $1;}
  ;

tyfields_nonempty:  tyfield {$$ = new absyn::FieldList($1);}
  |   tyfields_nonempty COMMA tyfield {$$ = $3->Prepend($1);}
  ;
  
tyfield: ID COLON ID {$$ = new absyn::Field(scanner_.GetTokPos(), $1, $3);}
  ;

ty:   ID {$$ = new absyn::NameTy(scanner_.GetTokPos(), $1);}
  |   LBRACE tyfields RBRACE {$$ = new absyn::RecordTy(scanner_.GetTokPos(), $2);}
  |   ARRAY OF ID {$$ = new absyn::ArrayTy(scanner_.GetTokPos(), $3);}
  ;

fundec: fundec_one {$$ = new absyn::FunDecList($1);}
  |   fundec_one fundec {$$ = $2->Prepend($1);}
  ;

fundec_one: FUNCTION ID LPAREN tyfields RPAREN COLON ID EQ exp {$$ = new absyn::FunDec(scanner_.GetTokPos(), $2, $4, $7, $9);}
  |   FUNCTION ID LPAREN tyfields RPAREN EQ exp {$$ = new absyn::FunDec(scanner_.GetTokPos(), $2, $4, nullptr, $7);}
  ;
  