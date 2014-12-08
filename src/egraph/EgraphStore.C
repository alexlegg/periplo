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

#include "Egraph.h"
#include "SimpSATSolver.h"

using namespace periplo;

void Egraph::initializeStore( )
{
	//
	// Reserve room for at least 65536 nodes
	//
	id_to_enode.reserve( 65536 );
	assert( config.logic != UNDEF );
	//
	// Create default sorts
	//
	Snode * sbool1  = sort_store.mkBool( );
	Snode * sparA1  = sort_store.mkPara( "_A_" );
	Snode * sparB1  = sort_store.mkPara( "_B_" );
	//
	// Some useful shortcuts
	//
	Snode * sbool1_list  = sort_store.cons( sbool1 );
	Snode * sbool2_list  = sort_store.cons( sbool1, sbool1_list );
	Snode * sbool2 = sort_store.mkDot( sbool2_list );
	Snode * sparA2 = sort_store.mkDot( sort_store.cons( sparA1, sort_store.cons( sparA1 ) ) );
	//
	// Allocates predefined symbols
	//
	newSymbol( "true"  , NULL, sbool1 ); assert( ENODE_ID_TRUE    == id_to_enode.size( ) - 1 );
	newSymbol( "false" , NULL, sbool1 ); assert( ENODE_ID_FALSE   == id_to_enode.size( ) - 1 );
	//
	// Core
	//
	newSymbol( "not"     , sbool1     , sbool1 ); assert( ENODE_ID_NOT      == id_to_enode.size( ) - 1 );
	newSymbol( "=>"      , sbool2     , sbool1 ); assert( ENODE_ID_IMPLIES  == id_to_enode.size( ) - 1 );
	newSymbol( "and"     , sbool2     , sbool1 ); assert( ENODE_ID_AND      == id_to_enode.size( ) - 1 );
	newSymbol( "or"      , sbool2     , sbool1 ); assert( ENODE_ID_OR       == id_to_enode.size( ) - 1 );
	newSymbol( "xor"     , sbool2     , sbool1 ); assert( ENODE_ID_XOR      == id_to_enode.size( ) - 1 );
	newSymbol( "="       , sparA2     , sbool1 ); assert( ENODE_ID_EQ       == id_to_enode.size( ) - 1 );
	//
	// Set top node to empty
	//
	top = NULL;
	//
	// Allocate true and false
	//
	etrue  = allocTrue ( );
	efalse = allocFalse( );
	//
	// Inserts true and false in signature table
	//
	insertSigTab( etrue );
	insertSigTab( efalse );
}

//
// Allocates true
//
Enode * Egraph::allocTrue ( )
{
	Enode * res = cons( id_to_enode[ ENODE_ID_TRUE ] );
	assert( res );
	assert( res->isTerm( ) );
#ifdef PRODUCE_PROOF
	// Not using config.produce_inter flag as not yet set
	// True/False are shared over all partitions
	ipartitions_t mask = -1;
	res->setIPartitions( mask );
#endif
	return res;
}

//
// Allocates false
//
Enode * Egraph::allocFalse ( )
{
	Enode * res = cons( id_to_enode[ ENODE_ID_FALSE ] );
	assert( res );
	assert( res->isTerm( ) );
#ifdef PRODUCE_PROOF
	// Not using config.produce_inter flag as not yet set
	// True/False are shared over all partitions
	ipartitions_t mask = -1;
	res->setIPartitions( mask );
#endif
	return res;
}

//
// Inserts a symbol
//
void Egraph::insertSymbol( Enode * s )
{
	assert( s );
	assert( s->isSymb( ) );
	// Consistency for id
	assert( (enodeid_t)id_to_enode.size( ) == s->getId( ) );
	// Symbol is not there
	assert( name_to_symbol.find( s->getNameFull( ) ) == name_to_symbol.end( ) );
	// Insert Symbol
	name_to_symbol[ s->getNameFull( ) ] = s;
	id_to_enode .push_back( s );
}

//
// Removes a symbol
//
void Egraph::removeSymbol( Enode * s )
{
	assert( s->isSymb( ) );
	assert( config.incremental );
	map< string, Enode * >::iterator it = name_to_symbol.find( s->getName( ) );
	assert( it != name_to_symbol.end( ) );
	assert( it->second == s );
	name_to_symbol.erase( it );
	id_to_enode[ s->getId( ) ] = NULL;
	delete s;
}


//
// Retrieves a symbol from the name
//
Enode * Egraph::lookupSymbol( const char * name )
{
	assert( name );
	map< string, Enode * >::iterator it = name_to_symbol.find( name );
	if ( it == name_to_symbol.end( ) ) return NULL;
	return it->second;
}

//
// Retrieves a define
//
Enode * Egraph::lookupDefine( const char * name )
{
	assert( name );
	map< string, Enode * >::iterator it = name_to_define.find( name );
	if ( it == name_to_define.end( ) ) return NULL;
	return it->second;
}

//
// Store a define
//
void Egraph::insertDefine( const char * n, Enode * d )
{
	assert( d );
	assert( n );
	assert( d->isDef( ) );
	assert( (enodeid_t)id_to_enode.size( ) == d->getId( ) );
	assert( name_to_define.find( n ) == name_to_define.end( ) );
	name_to_define[ n ] = d;
	id_to_enode.push_back( d );
}

//
// Insert into signature table possibly creating a new node
//
Enode * Egraph::insertSigTab ( const enodeid_t id, Enode * car, Enode * cdr )
{
	assert( car == car->getRoot( ) );
	assert( cdr == cdr->getRoot( ) );

#ifdef BUILD_64
	enodeid_pair_t sig = encode( car->getCid( ), cdr->getCid( ) );
#else
	const Pair( enodeid_t ) sig = make_pair( car->getCid( ), cdr->getCid( ) );
#endif
	Enode * res = sig_tab.lookup( sig );

	if ( res == NULL )
	{
		Enode * e = new Enode( id, car, cdr );
		sig_tab.insert( e );
		return e;
	}

	return res;
}

//
// Insert into Store
//
Enode * Egraph::insertStore( const enodeid_t id, Enode * car, Enode * cdr )
{
	static Enode* new_enode = NULL;

	if (new_enode == NULL)
		new_enode = new Enode( id, car, cdr );
	else {
		new_enode->~Enode();
		new_enode = new(new_enode) Enode( id, car, cdr);
	}

	Enode * x = store.insert( new_enode );
	// Node already there
	if ( x != new_enode ) return x;
	// Insertion done
	new_enode = NULL;
	return x;
}

//
// Remove from Store
//
void Egraph::removeStore( Enode * e )
{
	assert( e );
	store.remove( e );
}

//
// Retrieve element from signature table
//
Enode * Egraph::lookupSigTab ( Enode * e )
{
	Enode * res = sig_tab.lookup( e->getSig( ) );
	return res;
}

//
// Adds element to signature table
//
Enode * Egraph::insertSigTab ( Enode * e )
{
	sig_tab.insert( e );
	return e;
}

//
// Remove element from signature table
//
void Egraph::removeSigTab ( Enode * e )
{
	assert( lookupSigTab( e ) );
	sig_tab.erase( e );
}

//
// Copy list into a new one whose elements are retrieved from the cache
//

Enode * Egraph::copyEnodeEtypeListWithCache( Enode * l, bool map2 )
{
	assert(  map2 || active_dup_map1 );
	assert( !map2 || active_dup_map2 );

	list< Enode * > new_args;
	for ( Enode * arg = l ; !arg->isEnil( ) ; arg = arg->getCdr( ) )
	{
		new_args.push_front( map2
				? valDupMap2( arg->getCar( ) )
						: valDupMap1( arg->getCar( ) )
		);
	}

	Enode * res = cons( new_args );
	return res;
}

//
// Create a new term of the same kind but using info in the cache and
// also performs some simplifications
//
Enode * Egraph::copyEnodeEtypeTermWithCache( Enode * term, bool map2 )
{
	assert(  map2 || active_dup_map1 );
	assert( !map2 || active_dup_map2 );
	Enode * ll = copyEnodeEtypeListWithCache( term->getCdr( ), map2 );
	assert( ll->isList( ) );
	//
	// Case
	//
	if ( term->isAnd        ( ) ) return mkAnd       ( ll );
	if ( term->isOr         ( ) ) return mkOr        ( ll );
	if ( term->isNot        ( ) ) return mkNot       ( ll );
	if ( term->isImplies    ( ) ) return mkImplies   ( ll );
	if ( term->isXor        ( ) ) return mkXor       ( ll );

	if ( term->isVar( ) || term->isConstant( ) )
		return term;

	//
	// Enable if you want to make sure that your case is handled
	//
	// error( "Please add a case for ", term->getCar( ) );

	Enode * new_term = cons( term->getCar( ), ll );
	return new_term;
}

//
// FIXME: This is a little bit counter intuitive
// The list given is now in reverse order w.r.t.
// the returned one, they should insted be the
// same, more logical. But that implies that we
// have to modify other parts of the code, so
// be careful
//
Enode * Egraph::cons( list< Enode * > & args )
{
	Enode * elist = const_cast< Enode * >( enil );

	for ( list< Enode * >::iterator it = args.begin( )
			; it != args.end( )
			; it ++ )
		elist = cons( *it, elist );

	return elist;
}

Enode * Egraph::cons( Enode ** args, unsigned count )
{
	Enode * elist = const_cast< Enode * >( enil );

	for ( unsigned i = count; i > 0; --i) {
		elist = cons( args[i-1], elist );
	}
	return elist;
}

//
// Creates a new term and its correspondent modulo equivalence
//
Enode * Egraph::cons( Enode * car, Enode * cdr )
{
	assert( car );
	assert( cdr );
	assert( car->isTerm( ) || car->isSymb( ) );
	assert( cdr->isList( ) );
	Enode * e = NULL;
	// Create and insert a new enode if necessary
	e = insertStore( id_to_enode.size( ), car, cdr );
	assert( e );
	// The node was there already. Return it
	if ( (enodeid_t)id_to_enode.size( ) != e->getId( ) )
		return e;

	/*
	 * Had to disable because of problems
	 * connected with incrementality.
	 * It seems that a node
	 * after it is removed still survive in the
	 * signature tab, causing obvious inconsistencies
	 * in the invariants
	 *
	 * NOTE TO BE CLARIFIED !
	 *
  if ( config.incremental )
  {
    // Save Backtrack information
    undo_stack_term.push_back( e );
    undo_stack_oper.push_back( INSERT_STORE );
  }
	 */

	// We keep the created enode
	id_to_enode.push_back( e );
	return e;
}

//
// Create a variable
//
Enode * Egraph::mkVar( const char * name, bool model_var )
{
	Enode * e = lookupSymbol( name );
	// Not a variable, is it a define ?
	if ( e == NULL )
	{
		e = lookupDefine( name );
		// Not a define, abort
		if ( e == NULL )
			periplo_error2( "undeclared identifier ", name );
		assert( e->isDef( ) );
		// It's a define, return itss definition
		return e->getDef( );
	}
	// It's a variable
	Enode * res = cons( e );
	if ( model_var )
		variables.insert( res );
	return res;
}

Enode * Egraph::mkFun( const char * name, Enode * args )
{
	assert( args->isList( ) );
	//
	// Retrieve sort from arguments
	//
	stringstream ss;
	ss << name;
	for ( Enode * l = args ; !l->isEnil( ) ; l = l->getCdr( ) )
	{
		ss << " ";
		l->getCar( )->getRetSort( )->print( ss );
	}

	Enode * e = lookupSymbol( ss.str( ).c_str( ) );
	if ( e == NULL ) periplo_error2( "undeclared function symbol ", ss.str( ).c_str( ) );

	Enode * ret = cons( e, args );
	return ret;
}

//
// Creates a new symbol. Name must be new
//
Enode * Egraph::newSymbol( const char * name
		, Snode * args
		, Snode * retv
		, uint64_t )            // parameter for properties, not used now
{
	assert( retv );
	assert( retv->isTerm( ) );
	assert( args == NULL || args->isTerm( ) );

	stringstream ss;
	ss << name;
	if ( args ) ss << " " << args->getArgs( );

	if ( lookupSymbol( ss.str( ).c_str( ) ) != NULL )
		periplo_error2( "symbol already declared ", ss.str( ).c_str( ) );

	Enode * new_enode = new Enode( id_to_enode.size( ), ss.str( ).c_str( ), ETYPE_SYMB, args, retv );

	insertSymbol( new_enode );
	assert( lookupSymbol( ss.str( ).c_str( ) ) == new_enode );
	return new_enode;
}

Enode * Egraph::getDefine( const char * name )
{
	Enode * e = lookupDefine( name );
	assert( e );
	assert( e->getCar( ) != NULL );
	return e->getCar( );
}

void Egraph::mkDefine( const char * name, Enode * def )
{
	Enode * e = lookupDefine( name );
	if( e == NULL )
	{
		Enode * new_enode = new Enode( id_to_enode.size( ), def );
		insertDefine( name, new_enode );
	}
	else
	{
		// This symbol has been declared before. We just
		// replace its definition with this new one
		e->setDef( def );
	}
}

Enode * Egraph::mkNot( Enode * args )
{
	assert( args );
	assert( args->isList( ) );
	assert( args->getCar( ) );
	Enode * arg = args->getCar( );
	assert( arg->hasSortBool( ) );
	assert( arg->isTerm( ) );

	// not not p --> p
	if ( arg->isNot( ) )
		return arg->get1st( );

	// not false --> true
	if ( arg->isFalse( ) )
		return mkTrue( );

	// not true --> false
	if ( arg->isTrue( ) )
		return mkFalse( );

	return cons( id_to_enode[ ENODE_ID_NOT ], args );
}

Enode * Egraph::mkAnd( Enode * args )
{
	assert( args );
	assert( args->isList( ) );

	// Prepare + fast path
	unsigned count = 0;
	Enode *res = NULL;
	for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
	{
		Enode * e = alist->getCar( );
		assert( e->hasSortBool( ) );

		if ( e->isFalse( ) )
			return mkFalse();
		if ( e->isTrue( ) ) continue;
		res = e;
		count++;
	}
	if ( count == 0 )
		return mkTrue( );
	if ( count == 1 )
		return res;

	Enode** new_args = (Enode**) malloc(count*sizeof(Enode*));
	count = 0;

	// Filter duplicates
	initDup1( );
	for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
	{
		Enode * e = alist->getCar( );

		if ( e->isTrue( ) ) continue;
		if ( isDup1( e ) ) continue;

		new_args[count] = e;
		storeDup1( e );
		count++;
	}

	assert (count != 0);

	// Make the cons
	doneDup1( );

	res = NULL;

	Enode* rval;
	if ( count == 1 )
		rval = new_args[0];
	else
		rval = cons( id_to_enode[ ENODE_ID_AND ], cons( new_args, count ) );
	free(new_args);
	return rval;
}

Enode * Egraph::mkOr( Enode * args )
{
	assert( args );
	assert( args->isList( ) );

	// Prepare + fast path
	unsigned count = 0;
	Enode* res = NULL;
	for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
	{
		Enode * e = alist->getCar( );
		assert( e->hasSortBool( ) );

		if ( e->isTrue( ) )
			return mkTrue();
		if ( e->isFalse( ) ) continue;
		res = e;
		count++;
	}
	if ( count == 0 )
		return mkFalse( );
	if ( count == 1 )
		return res;

	Enode** new_args = (Enode**) malloc(count*sizeof(Enode*));
	count = 0;

	// Filter duplicates
	initDup1( );
	for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
	{
		Enode * e = alist->getCar( );

		if ( e->isFalse( ) ) continue;
		if ( isDup1( e ) ) continue;

		new_args[count] = e;
		storeDup1( e );
		count++;
	}

	assert (count != 0);

	// Make the cons
	doneDup1( );

	res = NULL;

	Enode* rval;
	if ( count == 1 )
		rval = new_args[0];
	else
		rval = cons( id_to_enode[ ENODE_ID_OR ], cons( new_args, count ) );
	free(new_args);
	return rval;
}

Enode * Egraph::mkIff( Enode * args )
{
	assert( args );
	assert( args->getArity( ) == 2 );
	Enode * first  = args->getCar( );
	Enode * second = args->getCdr( )->getCar( );

	if ( first ->isTrue ( ) )               return second;
	if ( first ->isFalse( ) )               return mkNot( cons( second ) );
	if ( second->isTrue ( ) )               return first;
	if ( second->isFalse( ) )               return mkNot( cons( first ) );
	if ( first == second )                  return mkTrue ( );
	if ( first == mkNot( cons( second ) ) ) return mkFalse( );

	return cons( id_to_enode[ ENODE_ID_EQ ], args );
}

Enode * Egraph::mkXor( Enode * args )
{
	assert( args );

	assert( args->getArity( ) == 2 );
	Enode * first  = args->getCar( );
	Enode * second = args->getCdr( )->getCar( );
	assert( first->hasSortBool( ) );
	assert( second->hasSortBool( ) );

	if ( first ->isFalse( ) )               return second;
	if ( first ->isTrue ( ) )               return mkNot( cons( second ) );
	if ( second->isFalse( ) )               return first;
	if ( second->isTrue ( ) )               return mkNot( cons( first ) );
	if ( first == second )                  return mkFalse( );
	if ( first == mkNot( cons( second ) ) ) return mkTrue ( );

	return cons( id_to_enode[ ENODE_ID_XOR ], args );
}

Enode * Egraph::mkImplies( Enode * args )
{
	assert( args );

	Enode * first  = args->getCar( );
	Enode * second = args->getCdr( )->getCar( );
	Enode * not_first = mkNot( cons( first ) );

	if ( first ->isFalse( ) ) return mkTrue( );
	if ( second->isTrue ( ) ) return mkTrue( );
	if ( first ->isTrue ( ) ) return second;
	if ( second->isFalse( ) ) return not_first;

	return mkOr( cons( not_first
			, cons( second ) ) );
}



//=================================================================================================
// Other APIs

//
// Packs assertions and formula and return it into a single enode
//
Enode * Egraph::getUncheckedAssertions( )
{
	if ( assertions.empty( ) ) return mkTrue( );
	// Pack the formula and the assertions
	// into an AND statement, and return it
	if ( top != NULL ) assertions.push_back( top );
	Enode * args = cons( assertions );
	// Clear assertions for incremental solving
	assertions.clear( );
	return mkAnd( args );
}

#ifdef PRODUCE_PROOF
Enode * Egraph::getNextAssertion( )
{
	if ( assertions.empty( ) ) return NULL;
	Enode * ret = assertions.front( );
	assertions.pop_front( );
	return ret;
}

void Egraph::addDefinition( Enode * def, Enode * term )
{
	assert( config.produce_inter != 0 );
	idef_list.push_back( def );
	assert( idef_map.find( def ) == idef_map.end( ) );
	idef_map[ def ] = term;
}

Enode * Egraph::expandDefinitions( Enode * interpolant )
{
	assert( interpolant );
	set< Enode * > idefs_to_undo;
	// Collect all definitions
	scanForDefs( interpolant, idefs_to_undo );
	Enode * result = interpolant;
	// Undo definitions
	for ( int i = idef_list.size( ) - 1 ; i >= 0 ; i -- )
	{
		Enode * def = idef_list[ i ];
		// Skip definitions not there
		if ( idefs_to_undo.find( def ) == idefs_to_undo.end( ) )
			continue;

		// Replace
		map< Enode *, Enode * > tmp_map;
		tmp_map[ def ] = idef_map[ def ];
		result = substitute( result, tmp_map );
		// Update defs to undo
		scanForDefs( result, idefs_to_undo );
	}

	return result;
}

void Egraph::scanForDefs( Enode * formula, set< Enode * > & idefs_to_undo )
{
	assert( formula );
	vector< Enode * > unprocessed_enodes;
	initDup1( );

	unprocessed_enodes.push_back( formula );
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		//
		// Skip if the node has already been processed before
		//
		if ( isDup1( enode ) )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( )
				; arg_list != enil
				; arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );

			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( !isDup1( arg ) )
			{
				unprocessed_enodes.push_back( arg );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children )
			continue;

		map< Enode *, Enode * >::iterator it = idef_map.find( enode );

		if ( it != idef_map.end( ) )
			idefs_to_undo.insert( enode );

		storeDup1( enode );
	}

	doneDup1( );
}

Enode * Egraph::substitute( Enode * formula, map< Enode *, Enode * > & substs )
{
	assert( formula );
	vector< Enode * > unprocessed_enodes;
	initDupMap1( );

	unprocessed_enodes.push_back( formula );
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		//
		// Skip if the node has already been processed before
		//
		if ( valDupMap1( enode ) != NULL )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( )
				; arg_list != enil
				; arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );

			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( valDupMap1( arg ) == NULL )
			{
				unprocessed_enodes.push_back( arg );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children )
			continue;

		map< Enode *, Enode * >::iterator it = substs.find( enode );

		Enode * result = NULL;
		if ( it != substs.end( ) )
		{
			assert( enode->isVar( ) );
			result = it->second;
		}
		else
			result = copyEnodeEtypeTermWithCache( enode );

		assert( result );
		storeDupMap1( enode, result );
	}

	Enode * new_formula = valDupMap1( formula );
	doneDupMap1( );

	assert( new_formula );
	return new_formula;
}
#endif

//
// Computes the polarities for theory atoms and
// set the decision polarity
// Nodes with both polarities gets a random polarity
//
void Egraph::computePolarities( Enode * formula )
{
	// Polarity will be all true or all false or all random
	return;

	assert( config.logic != UNDEF );

	vector< Enode * > unprocessed_enodes;
	initDup1( );

	unprocessed_enodes  .push_back( formula );
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		unprocessed_enodes  .pop_back( );
		//
		// Skip if the node has already been processed before
		//
		if ( isDup1( enode ) )
			continue;

		//
		// Process children
		//
		if ( enode->isBooleanOperator( ) )
		{
			Enode * arg_list;
			for ( arg_list = enode->getCdr( )
					; !arg_list->isEnil( )
					; arg_list = arg_list->getCdr( ) )
			{
				Enode * arg = arg_list->getCar( );
				assert( arg->isTerm( ) );
				unprocessed_enodes  .push_back( arg );
			}

			storeDup1( enode );
			continue;
		}

		assert( false );
	}

	// Done with cache
	doneDup1( );
}

void Egraph::addAssertion( Enode * e )
{
	assert( e );
	assertions.push_back( e );

#ifdef PRODUCE_PROOF
	// Tag formula for interpolation
	// (might not be necessary, but we do it)
	assert( formulae_to_tag.empty( ) );
	formulae_to_tag.push_back( assertions.back( ) );
	addIFormula( );
	formulae_to_tag.clear( );
#endif

	assert( !assertions.empty( ) );
}

//
// Maximize and/or and simplify if possible
//
Enode * Egraph::maximize( Enode * e )
{
	initDupMap1( );
	vector< Enode * > unprocessed_enodes;

	unprocessed_enodes.push_back( e );
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		//
		// Skip if the node has already been processed before
		//
		if ( valDupMap1( enode ) != NULL )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( )
				; !arg_list->isEnil( )
				; arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );
			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( valDupMap1( arg ) == NULL )
			{
				unprocessed_enodes.push_back( arg );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children )
			continue;

		unprocessed_enodes.pop_back( );
		Enode * result = NULL;
		//
		// Maximize and
		//
		if ( enode->isAnd( )
				|| enode->isOr( ) )
		{
			initDup2( );
			list< Enode * > new_list;

			Enode * arg_list;
			for ( arg_list = enode->getCdr( )
					; !arg_list->isEnil( ) && result == NULL
					; arg_list = arg_list->getCdr( ) )
			{
				// Retrieve simplified term
				Enode * arg = valDupMap1( arg_list->getCar( ) );

				if ( ( enode->isAnd( ) && arg->isAnd( ) )
						|| ( enode->isOr ( ) && arg->isOr ( ) ) )
				{
					Enode * arg_arg_list;
					for ( arg_arg_list = arg->getCdr( )
							; !arg_arg_list->isEnil( ) && result == NULL
							; arg_arg_list = arg_arg_list->getCdr( ) )
					{
						// cerr << "arg_arg_list car: " << arg_arg_list->getCar( ) << endl;
						// cerr << "              id: " << arg_arg_list->getCar( )->getId( ) << endl;
						// Retrieve simplified term
						// Enode * arg_arg = valDupMap1( arg_arg_list->getCar( ) );
						Enode * arg_arg = arg_arg_list->getCar( );
						assert( arg_arg );
						// cerr << "arg_arg: " << arg_arg << endl;

						// Skip duplicates
						if ( isDup2( arg_arg ) )
							continue;

						if ( arg_arg->isTrue( ) )
						{
							// Skip uninfluent
							if ( enode->isAnd( ) )
								continue;
							// It's true
							else
								result = mkTrue( );
						}
						else if ( arg_arg->isFalse( ) )
						{
							// Skip uninfluent
							if ( enode->isOr( ) )
								continue;
							// It's false
							else
								result = mkFalse( );
						}

						/*
						 * Causes problems as it creates new nodes
						 *
	    // !arg was processed before ...
	    if ( !arg->isNot( )
	      && isDup2( mkNot( cons( arg ) ) ) )
	    {
	      if ( enode->isOr( ) )
		result = mkTrue( );
	      else
		result = mkFalse( );
	    }
						 */

						// arg was processed before ...
						if ( arg_arg->isNot( )
								&& isDup2( arg_arg->get1st( ) ) )
						{
							if ( enode->isOr( ) )
								result = mkTrue( );
							else
								result = mkFalse( );
						}

						storeDup2( arg_arg );
						new_list.push_front( arg_arg );
					}
				}
				else
				{
					// Skip duplicates
					if ( isDup2( arg ) )
						continue;

					if ( arg->isTrue( ) )
					{
						// Skip uninfluent
						if ( enode->isAnd( ) )
							continue;
						// It's true
						else
							result = mkTrue( );
					}
					else if ( arg->isFalse( ) )
					{
						// Skip uninfluent
						if ( enode->isOr( ) )
							continue;
						// It's false
						else
							result = mkFalse( );
					}

					/*
					 * Causes problems as it creates new nodes
					 *
	  // !arg was processed before ...
	  if ( !arg->isNot( )
	  && isDup2( mkNot( cons( arg ) ) ) )
	  {
	  if ( enode->isOr( ) )
	  result = mkTrue( );
	  else
	  result = mkFalse( );
	  }
					 */

					// arg was processed before ...
					if ( arg->isNot( )
							&& isDup2( arg->get1st( ) ) )
					{
						if ( enode->isOr( ) )
							result = mkTrue( );
						else
							result = mkFalse( );
					}

					storeDup2( arg );
					new_list.push_front( arg );
				}
			}

			doneDup2( );

			if ( result == NULL )
				result = cons( enode->getCar( ), cons( new_list ) );
		}
		else
		{
			result = copyEnodeEtypeTermWithCache( enode );
		}

		assert( valDupMap1( enode ) == NULL );
		storeDupMap1( enode, result );
	}

	Enode * new_e = valDupMap1( e );
	assert( new_e );
	doneDupMap1( );

	return new_e;
}


#ifdef PRODUCE_PROOF
void Egraph::addIFormula( )
{
	// tagIFormulae( SETBIT( iformula ) );
	ipartitions_t partition = 0;
	setbit( partition, iformula );
	tagIFormulae( partition );
	iformula ++;
}

void Egraph::tagIFormulae( const ipartitions_t & partitions )
{
	if ( config.produce_inter == 0 )
		return;
	assert( partitions != 0 );
	tagIFormulae( partitions, formulae_to_tag );
}

void Egraph::tagIFormulae( const ipartitions_t & partitions, vector< Enode * > & f_to_tag )
{
	if ( config.produce_inter == 0 )return;

	initDup1( );
	while( !f_to_tag.empty( ) )
	{
		Enode * enode = f_to_tag.back( );

		if ( isDup1( enode ) )
		{
			f_to_tag.pop_back( );
			continue;
		}

		bool unprocessed_children = false;

		Enode * arg_list;
		for ( arg_list = enode->getCdr( )
				; !arg_list->isEnil( )
				; arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );
			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( !isDup1( arg ) )
			{
				f_to_tag.push_back( arg );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children )
			continue;

		f_to_tag.pop_back( );

		// Tag only up to predicates
		if ( !enode->isBooleanOperator( ) )
			enode->addIPartitions( partitions );
		// Tag symbol as well ...
		if ( enode->isUf( ) || enode->isUp( ) )
			enode->getCar( )->addIPartitions( partitions );

		storeDup1( enode );
	}

	doneDup1( );
}

void
Egraph::tagIFormula( Enode * e, const ipartitions_t & partitions )
{
	vector< Enode * > f_to_tag;
	f_to_tag.push_back( e );
	tagIFormulae( partitions, f_to_tag );
}
#endif



//=================================================================================================
// Debugging Routines

void Egraph::printMemStats( ostream & os )
{
	unsigned total = 0;

	for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
	{
		Enode * e = id_to_enode[ i ];
		assert( e != NULL );
		total += e->sizeInMem( );
	}

	os << "# " << endl;
	os << "# General Statistics" << endl;
	os << "#" << endl;
	os << "# Total enodes..........: " << id_to_enode.size( ) << endl;
	os << "# Enode size in memory..: " << ( total / 1048576.0 ) << " MB" << endl;
	os << "# Avg size per enode....: " << ( total / id_to_enode.size( ) ) << " B" << endl;
	os << "#" << endl;
	os << "# Splay Tree Statistics" << endl;
	store.printStatistics( os );
	os << "#" << endl;
	os << "# Signature Table Statistics" << endl;
	enodeid_t maximal;
	sig_tab.printStatistics( os, &maximal );
	os << "# Maximal node..........: " << id_to_enode[ maximal ] << endl;
	os << "#" << endl;
	os << "# Supporting data structures" << endl;
	os << "#" << endl;
	os << "# id_to_enode........: " << id_to_enode.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
	os << "# duplicates1........: " << duplicates1.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
	os << "# duplicates2........: " << duplicates2.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
	os << "# dup_map1...........: " << dup_map1.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
	os << "# dup_set1...........: " << dup_set1.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
	os << "# dup_map2...........: " << dup_map2.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
	os << "# dup_set2...........: " << dup_set2.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
	os << "# id_to_belong_mask..: " << id_to_belong_mask.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
	os << "# id_to_fan_in.......: " << id_to_fan_in.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
	os << "# cache..............: " << cache.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
	os << "# ext_store..........: " << ext_store.size( ) * sizeof( pair< pair< int, int >, Enode * > ) / 1048576.0 << " MB" << endl;
	os << "# se_store...........: " << se_store.size( ) * sizeof( pair< pair< int, int >, Enode * > ) / 1048576.0 << " MB" << endl;
	os << "# id_to_inc_edges....: " << id_to_inc_edges.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
	os << "#" << endl;

}

void Egraph::printEnodeList( ostream & os )
{
	os << "# =================================================" << endl;
	os << "# Enode Bank Information" << endl;
	os << "# " << endl;
	os << "# -----+-------------------------------------------" << endl;
	os << "# Enode Symbol List" << endl;
	os << "# -----+-------------------------------------------" << endl;
	for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
	{
		Enode * e = id_to_enode[ i ];

		if( e->getId( ) <= ENODE_ID_LAST )
			continue;

		if( e->isSymb( ) || e->isDef( ) )
		{
			// Print index formatted
			stringstream tmp; tmp << i;
			os << "# ";
			for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
			os << tmp.str( ) << " | ";

			e->print( os );
			os << endl;
		}
	}
	os << "# -----+-------------------------------------------" << endl;
	os << "# Enode Term List" << endl;
	os << "# -----+-------------------------------------------" << endl;
	for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
	{
		Enode * e = id_to_enode[ i ];
		if( e->isTerm( ) )
		{
			// Print index formatted
			stringstream tmp; tmp << i;
			os << "# ";
			for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
			os << tmp.str( ) << " | ";

			e->print( os );
			os << endl;
		}
	}
	os << "# -----+-------------------------------------------" << endl;
	os << "# Enode List List" << endl;
	os << "# -----+-------------------------------------------" << endl;
	for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
	{
		Enode * e = id_to_enode[ i ];
		if( e->isList( ) )
		{
			// Print index formatted
			stringstream tmp; tmp << i;
			os << "# ";
			for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
			os << tmp.str( ) << " | ";

			e->print( os );
			os << endl;
		}
	}
}

void Egraph::dumpAssertionsToFile( const char * filename )
{
	ofstream dump_out ( filename );
	dumpHeaderToFile  ( dump_out );
	dump_out << endl;
	for ( list< Enode * >::const_iterator ass_it = assertions.begin();
			ass_it != assertions.end();
			++ass_it) {
		dumpFormulaToFile ( dump_out, *ass_it );
	}
	dump_out << "(check-sat)" << endl;
	dump_out << "(exit)" << endl;
	dump_out.close( );
	cerr << "[Dumped " << filename << "]" << endl;
}

void Egraph::dumpToFileFunFrog( const char * filename )
{
	ofstream dump_out ( filename );
	dump_out << "(set-logic QF_BOOL)" << endl;
	dumpHeaderToFile  ( dump_out );
	dump_out << endl;
	for ( list< Enode * >::const_iterator ass_it = assertions.begin();
			ass_it != assertions.end();
			++ass_it) {
		dumpFormulaToFile ( dump_out, *ass_it );
	}
	dump_out << "(check-sat)" << endl;
	dump_out << "(get-interpolants)" << endl;
	dump_out << "(exit)" << endl;
	dump_out.close( );
	cerr << "[Dumped " << filename << "]" << endl;
}

void Egraph::dumpToFile( const char * filename, Enode * formula )
{
	ofstream dump_out ( filename );
	dumpHeaderToFile  ( dump_out );
	dump_out << endl;
	dumpFormulaToFile ( dump_out, formula );
	dump_out << "(check-sat)" << endl;
	dump_out << "(exit)" << endl;
	dump_out.close( );
	cerr << "[Dumped " << filename << "]" << endl;
}

void Egraph::dumpHeaderToFile( ostream & dump_out, logic_t l )
{
	if ( l == UNDEF ) l = config.logic;

	//NOTE comment away to use IDL interpolation with z3 for UFIDL formulae
	//dump_out << "(set-logic " << logicStr( l ) << ")" << endl;

	dump_out << "(set-info :source |" << endl
			<< "Dumped with "
			<< PACKAGE_STRING
			<< " on "
			<< __DATE__ << "." << endl
			<< "|)"
			<< endl;
	dump_out << "(set-info :smt-lib-version 2.0)" << endl;
	// Dump sorts
	sort_store.dumpSortsToFile( dump_out );
	// Dump function declarations
	for ( map< string, Enode * >::iterator it = name_to_symbol.begin( )
			; it != name_to_symbol.end( )
			; it ++ )
	{
		Enode * s = it->second;
		// Skip predefined/parametric symbols
		if ( s->getId( ) <= ENODE_ID_LAST
				|| s->getName( ) == string( "select" )
				|| s->getName( ) == string( "store" )
				|| s->getName( ) == string( "diff" )
				|| s->getName( ) == string( "fake_interp" )
				|| s->getName( ) == string( "ite" ) )
			continue;
		dump_out << "(declare-fun " << s->getName( ) << " ";
		if ( s->getArgSort( ) )
			dump_out << s->getArgSort( );
		else
			dump_out << "()";
		dump_out << " " << s->getRetSort( ) << ")" << endl;
	}
}

void Egraph::dumpFormulaToFile( ostream & dump_out, Enode * formula, bool negate )
{
	vector< Enode * > unprocessed_enodes;
	map< enodeid_t, string > enode_to_def;
	unsigned num_lets = 0;

	unprocessed_enodes.push_back( formula );
	// Open assert
	dump_out << "(assert" << endl;
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		//
		// Skip if the node has already been processed before
		//
		if ( enode_to_def.find( enode->getId( ) ) != enode_to_def.end( ) )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( ); !arg_list->isEnil( ); arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );
			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( enode_to_def.find( arg->getId( ) ) == enode_to_def.end( ) && arg->isBooleanOperator( ) )
			{
				unprocessed_enodes.push_back( arg );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children ) continue;

		unprocessed_enodes.pop_back( );

		char buf[ 32 ];
		sprintf( buf, "?def%d", enode->getId( ) );

		// Open let
		dump_out << "(let ";
		// Open binding
		dump_out << "((" << buf << " ";

		if ( enode->getArity( ) > 0 ) dump_out << "(";
		dump_out << enode->getCar( );
		for ( Enode * list = enode->getCdr( ); !list->isEnil( ); list = list->getCdr( ) )
		{
			Enode * arg = list->getCar( );
			if ( arg->isBooleanOperator( ) )
				dump_out << " " << enode_to_def[ arg->getId( ) ];
			else
			{
				dump_out << " " << arg;
				if ( enode->isAnd( ) ) dump_out << endl;
			}
		}
		if ( enode->getArity( ) > 0 ) dump_out << ")";

		// Closes binding
		dump_out << "))" << endl;
		// Keep track of number of lets to close
		num_lets++;

		assert( enode_to_def.find( enode->getId( ) ) == enode_to_def.end( ) );
		enode_to_def[ enode->getId( ) ] = buf;
	}
	dump_out << endl;
	// Formula
	if ( negate ) dump_out << "(not ";
	dump_out << enode_to_def[ formula->getId( ) ] << endl;
	if ( negate ) dump_out << ")";
	// Close all lets
	for( unsigned n=1; n <= num_lets; n++ ) dump_out << ")";
	// Closes assert
	dump_out << ")" << endl;
}

/*void Egraph::dumpFormulaToFile( ostream & dump_out, Enode * formula, bool negate )
{
	vector< Enode * > unprocessed_enodes;
	map< enodeid_t, string > enode_to_def;

	unprocessed_enodes.push_back( formula );
	// Open assert and let
	dump_out << "(assert" << endl;
	dump_out << "(let (";
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		//
		// Skip if the node has already been processed before
		//
		if ( enode_to_def.find( enode->getId( ) ) != enode_to_def.end( ) )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( ); !arg_list->isEnil( ); arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );
			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( enode_to_def.find( arg->getId( ) ) == enode_to_def.end( ) && arg->isBooleanOperator( ) )
			{
				unprocessed_enodes.push_back( arg );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children ) continue;

		unprocessed_enodes.pop_back( );

		char buf[ 32 ];
		sprintf( buf, "?def%d", enode->getId( ) );

		// Open binding
		dump_out << "(" << buf << " ";

		if ( enode->getArity( ) > 0 ) dump_out << "(";
		dump_out << enode->getCar( );
		for ( Enode * list = enode->getCdr( ); !list->isEnil( ); list = list->getCdr( ) )
		{
			Enode * arg = list->getCar( );
			if ( arg->isBooleanOperator( ) )
				dump_out << " " << enode_to_def[ arg->getId( ) ];
			else
			{
				dump_out << " " << arg;
				if ( enode->isAnd( ) ) dump_out << endl;
			}
		}
		if ( enode->getArity( ) > 0 ) dump_out << ")";

		// Closes binding
		dump_out << ")" << endl;

		assert( enode_to_def.find( enode->getId( ) ) == enode_to_def.end( ) );
		enode_to_def[ enode->getId( ) ] = buf;
	}

	// Closes binding list
	dump_out << ")" << endl;
	// Formula
	if ( negate ) dump_out << "(not ";
	dump_out << enode_to_def[ formula->getId( ) ] << endl;
	if ( negate ) dump_out << ")";
	// Close let
	dump_out << ")";
	// Closes assert
	dump_out << ")" << endl;
}*/
