%{
  open HopixAST
  open Position

  (* version 2*)

%}
  
%token VAL TYPE EXTERN FUN REF AND WHILE IF THEN ELIF ELSE 
%token LPAREN RPAREN  RBRACKET LBRACKET LRARROW PIPE EQUAL CEQUAL LBRACE RBRACE ARROW ANTISLASH
%token EXCLPOINT QUESTIONMARK
%token COMMA COLON SEMICOLON AMPER UNDERSCORE
%token STAR SLASH MINUS PLUS
%token LOWEREQUAL LOWERTHAN GREATERTHAN GREATEREQUAL ORLOGIC ANDLOGIC
%token EOF
%token<string> INFIXID STRING TYPEVAR VARID CONSTRID
%token<char> CHAR 
%token<Int32.t> INT
%token<bool> BOOL


   
%right SEMICOLON
%nonassoc vdefi
%right LRARROW ARROW 
%nonassoc THEN 
%nonassoc ELSE ELIF CEQUAL
%left ORLOGIC br
%left PIPE ANDLOGIC
%nonassoc COLON LOWERTHAN GREATERTHAN GREATEREQUAL LOWEREQUAL  EQUAL
%left AMPER
%left INFIXID
%left PLUS MINUS
%left STAR SLASH
%right REF 
%left EXCLPOINT QUESTIONMARK


%start<HopixAST.t> program

%%

(************************************************************************** program parts ***************************************************)
program: def=located(definition) * EOF
{
   def
}

(************************************************************************** definition parts *************************************************)
definition:
| TYPE x=located(type_con)
{
	DefineType( x, [], HopixAST.Abstract )
}
| TYPE tc=located(type_con) ltv=delimited(LPAREN,separated_nonempty_list(COMMA,located(type_variable)), RPAREN)
{
	DefineType( tc, ltv, HopixAST.Abstract )
}
| TYPE tc=located(type_con) EQUAL td=tdefinition
{
	DefineType(tc, [], td)
}
| TYPE tc=located(type_con) ltv=delimited(LPAREN,separated_nonempty_list(COMMA,located(type_variable)), RPAREN) EQUAL td=tdefinition
{
	DefineType(tc, ltv, td)
}
| EXTERN id=located(var_id) COLON t=located(ttype)
{
	DeclareExtern(id,t)
}
| vdef=vdefinition
{
	vdef
}

(********************************************************************** Vdefintion parts ****************************************************)
vdefinition:
(** A toplevel definition for a value. *)
| v=val_def
{
	let x,e=v in
	DefineValue(x,e)
}
| VAL x=located(var_id) EQUAL e=located(expression)
{
	DefineValue(x,e)
}

(****)
| FUN id=located(var_id)  x=type_variable_list LPAREN p_list=separated_nonempty_list(COMMA, located(pattern)) RPAREN l=option(preceded(COLON, located(ttype))) EQUAL e=located(expression) v=vdeffun
{
   let start_f = match l with 
	| None -> (id,(x,p_list,e))
	| Some a -> let ta=(Position.with_poss $startpos $endpos (TypeAnnotation(e,a)))
        in (id,(x,p_list,ta))
           in
           let ls = start_f::v in 
              let l =
                List.map (fun (v_id, vdf) ->
                  let a,b,c = vdf in
                    (v_id, Position.with_poss $startpos $endpos (FunctionDefinition(a,b,c))) ) ls
              in
	      DefineRecFuns (l)
}



    
fun_def:
| FUN id=located(var_id)  x=type_variable_list LPAREN p_list=separated_nonempty_list(COMMA, located(pattern)) RPAREN l=option(preceded(COLON, located(ttype))) EQUAL e=located(expression) v=vdeffun
{
   let start_f = match l with 
	| None -> (id,(x,p_list,e))
	| Some a -> let ta=(Position.with_poss $startpos $endpos (TypeAnnotation(e,a)))
        in (id,(x,p_list,ta))
           in
           let ls = start_f::v in 
              let l =
                List.map (fun (v_id, vdf) ->
                  let a,b,c = vdf in
                    (v_id, Position.with_poss $startpos $endpos (FunctionDefinition(a,b,c))) ) ls
              in
	      l
}
    
(******************)
vdeffun:

| AND id = located(var_id) x=type_variable_list LPAREN p_list=separated_nonempty_list(COMMA, located(pattern)) RPAREN l=option(preceded(COLON, located(ttype))) EQUAL e=located(expression) v=vdeffun
{
    	match l with 
	| None -> (id,(x,p_list,e)) :: v
	| Some a -> let ta=(Position.with_poss $startpos $endpos (TypeAnnotation(e,a)))
                       in
                          (id,(x,p_list,ta)) :: v   
}
|   %prec vdefi
{
     []
}



type_variable_list:
| LBRACKET le= separated_nonempty_list(COMMA, located(type_variable)) RBRACKET
{
	le
}
|
{
	[]
}


val_def: 
| VAL v=located(var_id) COLON tip=located(ttype)  EQUAL e=located(expression)
{
	let ta = Position.with_poss $startpos $endpos (TypeAnnotation(e,tip))
	in (v,ta) 
}

(*************************************************************** tdefinition parts ********************************************************)
tdefinition:
| PIPE? td=separated_nonempty_list(PIPE, pair(located(constructor), loption(delimited(LPAREN, separated_nonempty_list(COMMA, located(ttype)), RPAREN ))))
{
	DefineSumType(td)
}
|
{
	Abstract
}

(*************************************************************** ttype parts ***************************************************************)
ttype:
| t=type_con  s=loption(delimited(LPAREN, separated_list(COMMA, located(ttype)), RPAREN))
{
	TyCon(t,s)
}	
| LPAREN t=ttype RPAREN
{
	t
}
| t1 = located(ttype) LRARROW t2 = located(ttype)
{
	TyCon ((TCon("->")),[t1;t2])
}
| e=type_variable
{
	TyVar e
}

(**************************************************************** expression parts **********************************************************)
expression:
| MINUS e2 = located(expression)
{
	let value_of_exp = function
		| Literal y -> y
		| _ -> failwith "error negative expression" in
	let x = value_of_exp e2.value
	in let value_of_literal = function
			| LInt x -> x 
			| _ -> failwith "error negative expression"
	in let z = value_of_literal x.value in
	Literal ({ e2 with value = LInt (Int32.of_string ("-"^(string_of_int (Int32.to_int z)) )) }) 
}
(** A local definition *)
| VAL x = located(var_id) EQUAL e1 = located(expression) SEMICOLON e2=located(expression)
{
	Define (x,e1,e2)
}
| v = val_def SEMICOLON e2=located(expression)
{
        let (x,e1) = v in Define (x,e1,e2)
}

| f = fun_def  SEMICOLON e2=located(expression)
{
        DefineRec (f,e2)
}
(** Construction d'une donnee etiquete **)
| c=located(constructor) e1=loption(delimited(LBRACKET, separated_nonempty_list(COMMA, located(ttype)), RBRACKET)) e2=loption(delimited(LPAREN,separated_nonempty_list(COMMA, located(expression)), RPAREN)) 
{
	Tagged(c,e1,e2)
}
(** Reference  *)
| REF e=located(expression)
{
	Ref e
}
(** Type Annotation *)
| LPAREN e=located(expression) COLON t=located(ttype) RPAREN 
{
	TypeAnnotation(e,t)
}
| EXCLPOINT e=located(expression)
{
	Read e
}
(** Boucle **)
| WHILE e1=located(expression) LBRACE e2=located(expression) RBRACE
{
        While (e1,e2)
}
(** Binoperation*)
| e1=located(expression) b_op=located(binop) e2=located(expression)
{
  let op = Position.(map (fun x -> Variable (map (fun _ -> Id x) b_op))) b_op in
    (Apply (op,[],[e1;e2]))
}
(** Affectation **)
| e1=located(expression) CEQUAL e2=located(expression)
{
       Write (e1,e2)
}
(** Séquancement **)
| e1=located(expression) SEMICOLON e2=located(expression)
{
      let loc x = Position.with_poss $startpos $endpos x in
       Define(loc (Id "nothing"), e1, e2)
}
(** Conditionnelle **)
| IF c=located(expression) THEN e1=located(expression) l_p=elif_expr
{
       let list_exp = (c,e1)::l_p  in
       If (list_exp,None)
}
| IF c=located(expression) THEN e1=located(expression) l_p=elif_expr ELSE e2=located(expression)
{
       let list_exp = (c,e1)::l_p  in
       If (list_exp,Some e2)
}
| IF c=located(expression) THEN e1=located(expression)
{
       let list_exp = (c,e1)::[]  in
       If (list_exp,None)
}
| IF c=located(expression) THEN e1=located(expression) ELSE e2=located(expression) 
{
       let list_exp = (c,e1)::[]  in
       If (list_exp,Some e2)
}
| e=located(expression) QUESTIONMARK bs=branches
{
       Case (e,bs)
}
(** fonction anonyme **)
| ANTISLASH x=type_variable_list LPAREN p_list=separated_nonempty_list(COMMA, located(pattern)) RPAREN ARROW e=located(expression)
{
	Fun (FunctionDefinition( x, p_list, e))
}
(** Simple_expression **)
| e=simple_expression
{
	e
}

(** elif expr then expr part **)    
elif_expr:
| ELIF c=located(expression) THEN e1=located(expression) l=elif_expr
{
       (c,e1)::l
}
| ELIF c=located(expression) THEN e1=located(expression)
{
       [(c,e1)]
}

(***************************************************************** simple_expression parts ********************************************)
simple_expression:
(**Application *)
| e=located(simple_expression) tl=loption(delimited(LBRACKET, separated_nonempty_list(COMMA, located(ttype)), RBRACKET)) LPAREN el=separated_nonempty_list(COMMA, located(expression)) RPAREN 
{
	Apply(e, tl, el)
}
(** Literals *)
| l = located(literal)
{
	Literal l
}
(** Variables *)
| v=located(var_id)
{

	Variable v
}
(** Parenthesis *)
| LPAREN e=expression RPAREN
{
	e
}

(******************************************* branches parts ************************************************************)
branches:
| PIPE? l_b=s_n_list(PIPE, located(branch))
{
         l_b
}
| LBRACE PIPE? l_b=s_n_list(PIPE, located(branch)) RBRACE
{
         l_b
}
    
branch:
| p=located(pattern) ARROW e=located(expression) %prec br
{
        Branch (p,e)
}

(************************************************************* pattern parts ***************************************************)
pattern:
(** Littéraux **)
| l=located(literal)
{
  PLiteral (l)
}
(** Motif universel liant **)
| i=located(var_id)
{
  PVariable (i)
}
(** Etiquette **)
| c=located(constructor)
{
  PTaggedValue(c,[])
}
(** Valeurs étiquetées **)
| c=located(constructor) LPAREN l=separated_nonempty_list(COMMA,located(pattern)) RPAREN
{
  PTaggedValue(c,l)
}
(** Parenthésage **)
| LPAREN p=pattern RPAREN
{
  p
}
(** Annotation de type **)
| p=located(pattern) COLON t=located(ttype)
{
  PTypeAnnotation(p,t)
}
(** Motif unversel non liant **)
| UNDERSCORE
{
  PWildcard
}
(** Disjonction **)
| lp=located(pattern) PIPE rp=located(pattern)
{
  let located x = Position.with_poss $startpos $endpos x in
  let f = match (Position.value lp),(Position.value rp) with
  | POr p1, POr p2 -> p1@p2
  | POr p1, p2 -> p1@[(located p2)]
  | p1, POr p2 -> (located p1)::p2
  | _, _ -> [lp;rp]
  in
  POr (f)
}
(** Conjonction **)    
| lp=located(pattern) AMPER rp=located(pattern)
{
  let located x = Position.with_poss $startpos $endpos x in
  let f = match (Position.value lp),(Position.value rp) with
  | PAnd p1, PAnd p2 -> p1@p2
  | PAnd p1, p2 -> p1@[(located p2)]
  | p1, PAnd p2 -> (located p1)::p2
  | _, _ -> [lp;rp]
  in
  PAnd (f)
}


%inline literal:
| n=INT
{
	LInt  n
}
| c=CHAR
{
	LChar c
}
| s=STRING
{
	LString s
}	
| b=BOOL
{
	LBool b
}

%inline binop:    
  x=INFIXID      { String.(sub x 0 (length x - 1)) }
| PLUS           { "`+"  }
| MINUS          { "`-"  }
| STAR           { "`*"  }
| SLASH          { "`/"  }
| GREATEREQUAL   { "`>=" }
| GREATERTHAN    { "`>"  }
| LOWERTHAN      { "`<"  }
| LOWEREQUAL     { "`<=" }
| EQUAL          { "`="  }
| ORLOGIC        { "`||" }
| ANDLOGIC       { "`&&" }



%inline type_con: ty = VARID
{
	match String.get ty 0 with
	| '`' -> failwith "expects constructor"
	| _ -> TCon ty
}

%inline var_id: i=VARID
{
	Id i
}

%inline type_variable: t=TYPEVAR
{
	TId t
}

%inline constructor: c=CONSTRID
{
	KId c
}

%inline located(X): x=X
{
	Position.with_poss $startpos $endpos x
}

s_n_list(separator, X):
x = X %prec br
{
      [ x ]
}
| x = X; separator; xs = s_n_list(separator, X)
{
      x :: xs
}
