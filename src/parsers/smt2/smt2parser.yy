/*********************************************************************
Author: Roberto Bruttomesso   <roberto.bruttomesso@gmail.com>
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso
PeRIPLO -- Copyright (C) 2013, Simone Fulvio Rollini

Periplo is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Periplo is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Periplo. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

%{
#include "Global.h"
#include "Egraph.h"
#include "SStore.h"
#include "PeriploContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int smt2lineno;
extern int smt2lex( );
extern periplo::PeriploContext * parser_ctx;

vector< string > * createNumeralList  ( const char * );
vector< string > * pushNumeralList    ( vector< string > *, const char * );
void		   destroyNumeralList ( vector< string > * );

list< periplo::Snode * > * createSortList  ( periplo::Snode * );
list< periplo::Snode * > * pushSortList    ( list< periplo::Snode * > *, periplo::Snode * );
void		  destroySortList ( list< periplo::Snode * > * );

void smt2error( const char * s )
{
  printf( "At line %d: %s\n", smt2lineno, s );
  exit( 1 );
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
  char  *                   str;
  vector< string > *        str_list;
  periplo::Enode *                   enode;
  periplo::Snode *                   snode;
  list< periplo::Snode * > *         snode_list;
  map< periplo::Enode *, periplo::Enode * > * binding_list;
}

%error-verbose

%token TK_NUM TK_DEC TK_HEX TK_STR TK_SYM TK_KEY TK_BIN
%token TK_BOOL
%token TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_DECLARESORT TK_DEFINESORT TK_DECLAREFUN
%token TK_PUSH TK_POP TK_CHECKSAT TK_GETASSERTIONS TK_GETPROOF TK_GETUNSATCORE TK_GETINTERPOLANTS
%token TK_GETVALUE TK_GETASSIGNMENT TK_GETOPTION TK_GETINFO TK_EXIT
%token TK_AS TK_LET TK_FORALL TK_EXISTS TK_ANNOT TK_DISTINCT TK_DEFINEFUN
%token TK_ASSERT 
%token TK_REAL TK_INT TK_ARRAY
%token TK_PLUS TK_MINUS TK_TIMES TK_UMINUS TK_DIV
%token TK_NE TK_EQ TK_LEQ TK_GEQ TK_LT TK_GT
%token TK_AND TK_OR TK_NOT TK_IFF TK_XOR TK_ITE TK_IFTHENELSE TK_IMPLIES
%token TK_TRUE TK_FALSE TK_INTERPOLATE
%token TK_BVSLT TK_BVSGT TK_BVSLE TK_BVSGE
%token TK_BVULT TK_BVUGT TK_BVULE TK_BVUGE
%token TK_EXTRACT TK_CONCAT TK_BVAND TK_BVOR TK_BVXOR TK_BVNOT TK_BVADD TK_BVNEG TK_BVMUL TK_BVASHR TK_REPEAT
%token TK_SIGN_EXTEND TK_ZERO_EXTEND TK_ROTATE_LEFT TK_ROTATE_RIGHT TK_BVLSHR TK_BVSHL TK_BVSREM TK_BVSDIV TK_BVSUB
%token TK_BVUDIV TK_BVUREM
%token TK_PRINT_SUCCESS TK_EXPAND_DEFINITIONS TK_INTERACTIVE_MODE TK_PRODUCE_PROOFS TK_PRODUCE_UNSAT_CORES TK_PRODUCE_INTERPOLANTS
%token TK_PRODUCE_MODELS TK_PRODUCE_ASSIGNMENTS TK_REGULAR_OUTPUT_CHANNEL TK_DIAGNOSTIC_OUTPUT_CHANNEL
%token TK_RANDOM_SEED TK_VERBOSITY
%token TK_STORE TK_SELECT TK_DIFF

%type <str> TK_NUM TK_DEC TK_HEX TK_STR TK_SYM TK_KEY numeral decimal hexadecimal binary symbol 
%type <str> identifier spec_const b_value s_expr
%type <str_list> numeral_list
%type <enode> term_list term
%type <snode> sort
%type <snode_list> sort_list

%start script

%%

script: command_list

command_list: command_list command | command ;

command: '(' TK_SETLOGIC symbol ')'
         { parser_ctx->SetLogic( $3 ); free( $3 ); }
       | '(' TK_SETOPTION option ')'
         { }
       | '(' TK_SETINFO TK_KEY ')'
	 { parser_ctx->SetInfo( $3 ); free( $3 ); }
       | '(' TK_SETINFO TK_KEY s_expr ')'
	 { parser_ctx->SetInfo( $3, $4 ); free( $3 ); free( $4 ); } 
       | '(' TK_DECLARESORT symbol numeral ')'
	 { parser_ctx->DeclareSort( $3, atoi($4) ); free( $3 ); free( $4 ); }
       | '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'
	 { 
	   periplo::Snode * a = parser_ctx->mkCons( *$5 );
	   periplo::Snode * s = parser_ctx->mkSort( a );
	   parser_ctx->DeclareFun( $3, s, $7 );
	   destroySortList( $5 ); free( $3 );
	 }
       | '(' TK_DECLAREFUN symbol '(' ')' sort ')'
	 { parser_ctx->DeclareFun( $3, NULL, $6 ); free( $3 ); }
       | '(' TK_PUSH numeral ')'
	 { parser_ctx->addPush( atoi( $3 ) ); free( $3 ); }
       | '(' TK_POP numeral ')'
	 { parser_ctx->addPop( atoi( $3 ) ); free( $3 );}
       | '(' TK_ASSERT term ')'
         { parser_ctx->addAssert( $3 ); }
       | '(' TK_CHECKSAT ')'
	 { parser_ctx->addCheckSAT( ); }
       | '(' TK_GETPROOF ')'
	 { parser_ctx->addGetProof( ); }
       | '(' TK_GETINTERPOLANTS ')'
	 { parser_ctx->addGetInterpolants( ); }
       | '(' TK_EXIT ')'
         { parser_ctx->addExit( ); }
       ;

s_expr: spec_const 
	{ $$ = $1; } 
      | TK_SYM 
	{ $$ = $1; } 
      | TK_KEY 
        { $$ = $1; }
      /*
      | '(' s_expr ')' 
      */
      ;

spec_const: numeral 
	    { $$ = $1; }
	  | decimal 
	    { $$ = $1; }
	  | hexadecimal 
	    { $$ = $1; }
	  | binary
	    { $$ = $1; }
	  | TK_STR 
	    { $$ = $1; }
          ;

identifier: TK_SYM 
	    { $$ = $1; }
	  | '(' '_' TK_SYM numeral_list ')' 
	  ;

keyword: TK_KEY { free($1); };

symbol: TK_SYM 
        { $$ = $1; }
      ;

symbol_list: symbol_list symbol | symbol ;

attribute_value: spec_const { free($1); } | TK_SYM | '(' s_expr_list ')' | '(' ')' ;

sort: TK_BOOL 
      { $$ = parser_ctx->mkSortBool( ); }
    | identifier 
      { $$ = parser_ctx->mkSortVar( $1 ); free( $1 ); }
    | '(' identifier sort_list ')' 
      { 
        periplo::Snode * s = parser_ctx->mkCons( parser_ctx->mkSortVar( $2 ) ); 
	(*$3).push_front( s );
	$$ = parser_ctx->mkSort( parser_ctx->mkCons( *$3 ) );
        free( $2 ); 
      }
    ;

sorted_var: '(' TK_SYM sort ')' ;

term: 
  /* 
   * List of predefined identifiers 
   */
    TK_TRUE
      { $$ = parser_ctx->mkTrue( ); }
    | TK_FALSE
      { $$ = parser_ctx->mkFalse( ); }
    | '(' TK_AND term_list ')'
      { $$ = parser_ctx->mkAnd( $3 ); }
    | '(' TK_OR term_list ')'
      { $$ = parser_ctx->mkOr( $3 ); }
    | '(' TK_XOR term_list ')'
      { $$ = parser_ctx->mkXor( $3 ); }
    | '(' TK_NOT term_list ')'
      { $$ = parser_ctx->mkNot( $3 ); }
    | '(' TK_IMPLIES term_list ')'
      { $$ = parser_ctx->mkImplies( $3 ); }
    | '(' TK_LET '(' var_binding_list ')' term ')'
      { $$ = $6; }
  /*
   * Variable
   */
    | identifier 
      { $$ = parser_ctx->mkVar( $1 ); free( $1 ); }
  /*
   * Function application
   */
    | '(' identifier term_list ')'
      { $$ = parser_ctx->mkFun( $2, $3 ); free( $2 ); }
    ;

sort_list: sort_list sort 
	   { $$ = pushSortList( $1, $2 ); }
	 | sort 
	   { $$ = createSortList( $1 ); }
         ;

sorted_var_list: sorted_var_list sorted_var | sorted_var ;

var_binding_list: var_binding_list '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $3, $4 ); free($3); }
                | '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $2, $3 ); free($2); }
		;

term_list: term term_list
	   { $$ = parser_ctx->mkCons( $1, $2 ); }
	 | term 
           { $$ = parser_ctx->mkCons( $1 ); }
         ;

s_expr_list: s_expr_list s_expr | s_expr ;

numeral_list: numeral_list numeral
	      { $$ = pushNumeralList( $1, $2 ); }
	    | numeral
	      { $$ = createNumeralList( $1 ); }
	    ;

numeral: TK_NUM { $$ = $1; } ;

decimal: TK_DEC { $$ = $1; } ;

hexadecimal: TK_HEX { $$ = $1; } ;

binary: TK_BIN ;

option: TK_PRINT_SUCCESS b_value
        { 
	  parser_ctx->SetOption( ":print-success", $2 );
	  free( $2 );
        }
      | TK_EXPAND_DEFINITIONS b_value
	{
	  parser_ctx->SetOption( ":expand-definitions", $2 );
          free( $2 );
        }
      | TK_INTERACTIVE_MODE b_value
	{
	  parser_ctx->SetOption( ":interactive-mode", $2 );
          free( $2 );
        }
      | TK_PRODUCE_PROOFS b_value
	{
	  parser_ctx->SetOption( ":produce-proofs", $2 );
          free( $2 );
        }
      | TK_PRODUCE_UNSAT_CORES b_value
	{
	  parser_ctx->SetOption( ":produce-unsat-cores", $2 );
          free( $2 );
        }
      | TK_PRODUCE_INTERPOLANTS b_value
	{
	  parser_ctx->SetOption( ":produce-interpolants", $2 );
          free( $2 );
        }
      | TK_PRODUCE_MODELS b_value
	{
	  parser_ctx->SetOption( ":produce-models", $2 );
          free( $2 );
        }
      | TK_PRODUCE_ASSIGNMENTS b_value
	{
	  parser_ctx->SetOption( ":produce-assignments", $2 );
          free( $2 );
        }
      | TK_REGULAR_OUTPUT_CHANNEL TK_STR
	{
	  char buf[256] = ":regular-output-channel "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( ":regular-output-channel", $2 );
          free( $2 );
        }
      | TK_DIAGNOSTIC_OUTPUT_CHANNEL TK_STR
	{
	  parser_ctx->SetOption( ":diagnostic-output-channel", $2 );
          free( $2 );
        }
      | TK_RANDOM_SEED TK_NUM
	{
	  parser_ctx->SetOption( ":random-seed", $2 );
          free( $2 );
        }
      | TK_VERBOSITY TK_NUM
	{
	  parser_ctx->SetOption( ":verbosity", $2 );
          free( $2 );
	}
      | TK_KEY
	{ parser_ctx->SetOption( $1 ); free( $1 ); }
      | TK_KEY s_expr
	{ 
	  parser_ctx->SetOption( $1, $2 ); 
	  free( $1 ); free( $2 ); 
        }
      ;
      
b_value: TK_TRUE
         { 
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "true" );
	   $$ = buf;
         }
       | TK_FALSE
         {
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "false" );
	   $$ = buf;
	 }
       ;

%%

//=======================================================================================
// Auxiliary Routines

vector< string > * createNumeralList( const char * s )
{
  vector< string > * l = new vector< string >;
  l->push_back( s );
  return l;
} 

vector< string > * pushNumeralList( vector< string > * l, const char * s )
{
  l->push_back( s );
  return l;
}

void destroyNumeralList( vector< string > * l )
{
  delete l;
}

list< periplo::Snode * > * createSortList( periplo::Snode * s )
{
  list< periplo::Snode * > * l = new list< periplo::Snode * >;
  l->push_back( s );
  return l;
} 

list< periplo::Snode * > * pushSortList( list< periplo::Snode * > * l, periplo::Snode * s )
{
  l->push_back( s );
  return l;
}

void destroySortList( list< periplo::Snode * > * l )
{
  assert( l );
  delete l;
}
