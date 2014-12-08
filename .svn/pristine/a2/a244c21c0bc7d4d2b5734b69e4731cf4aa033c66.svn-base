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

#include "TopLevelProp.h"

using namespace periplo;

#define SIMPLIFY_TWIN_EQUALITIES 1

Enode *TopLevelProp::doit( Enode * formula )
{
	assert( formula );
	//
	// We don't currently keep track of substitutions
	//
#ifndef PRODUCE_PROOF
	//
	// Repeat until fix point
	//
	bool stop = false;
	// If our target is to dump a formula to interpolate - skip fixpoint
	if ( config.sat_dump_rnd_inter != 0 ) stop = true;
	list< Enode * > conj;
	while ( !stop )
	{
		if ( formula->isTrue( ) || formula->isFalse( ) )
		{
			stop = true;
			continue;
		}
		//
		// Step 1: gather top-level facts (including predicates)
		//
		map< Enode *, Enode * > substitutions;
		map< Enode *, Enode * > constant_substs;
		if ( !retrieveSubstitutions( formula, substitutions, constant_substs ) )
			return egraph.mkFalse( );
		//
		// Step 2: produce a new formula with substitutions done (if any to use)
		//
		bool sub_stop = true;

		// Normal substitutions
		if ( !substitutions.empty( ) )
			formula = substitute( formula, substitutions, sub_stop );

		stop = sub_stop;
	}

	// Reinsert back constants substitutions
	conj.push_back( formula );
	formula = egraph.mkAnd( egraph.cons( conj ) );

#endif
	return formula;
}

bool
TopLevelProp::retrieveSubstitutions( Enode * formula, map< Enode *, Enode * > & substitutions, map< Enode *, Enode * > & constant_substs )
{
	assert( substitutions.empty( ) );
	vector< Enode * > unprocessed_enodes;
	vector< bool >    unprocessed_polarity;
	vector< Enode * > top_level_arith;

	egraph.initDup1( );

	unprocessed_enodes  .push_back( formula );
	unprocessed_polarity.push_back( true );
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		assert( unprocessed_enodes.size( ) == unprocessed_polarity.size( ) );
		Enode * enode = unprocessed_enodes.back( );
		const bool polarity = unprocessed_polarity.back( );
		unprocessed_enodes  .pop_back( );
		unprocessed_polarity.pop_back( );
		//
		// Skip if the node has already been processed before
		//
		if ( egraph.isDup1( enode ) )
			continue;

		egraph.storeDup1( enode );
		//
		// Process children
		//
		if ( enode->isBooleanOperator( ) )
		{
			bool recurse = true;
			bool new_polarity;

			if ( enode->isAnd( ) && polarity )
				new_polarity = true;
			else if ( enode->isNot( ) )
				new_polarity = !polarity;
			else if ( enode->isOr( ) && !polarity )
				new_polarity = false;
			else
				recurse = false;

			if ( recurse )
			{
				Enode * arg_list;
				for ( arg_list = enode->getCdr( )
						; arg_list != egraph.enil
						; arg_list = arg_list->getCdr( ) )
				{
					Enode * arg = arg_list->getCar( );
					assert( arg->isTerm( ) );
					unprocessed_enodes  .push_back( arg );
					unprocessed_polarity.push_back( new_polarity );
				}
				continue;
			}
		}
		//
		// Add a new substitution for iff if possible
		//
		if ( enode->isIff( ) && polarity )
		{
			Enode * lhs = enode->get1st( );
			Enode * rhs = enode->get2nd( );

			if ( !lhs->isVar( ) && !rhs->isVar( ) )
				continue;

			Enode * var  = lhs->isVar( ) ? lhs : rhs;
			Enode * term = lhs->isVar( ) ? rhs : lhs;

			if ( contains( term, var ) )
				continue;

			// Substitute variable with term that does not contain it
			substitutions[ var ] = term;

			// Save substitution for retrieving model
			egraph.addSubstitution( var, term );
		}
		//
		// Add a new substitution for some boolean or theory atom if possible
		//
		else if ( enode->isAtom( ) )
		{
			if ( enode->isTrue( ) )
			{
				substitutions[ enode ] = egraph.mkTrue( );
				// Save substitution for retrieving model
				egraph.addSubstitution( enode, egraph.mkTrue( ) );
				continue;
			}

			if ( enode->isFalse( ) )
			{
				substitutions[ enode ] = egraph.mkFalse( );
				// Save substitution for retrieving model
				egraph.addSubstitution( enode, egraph.mkFalse( ) );
				continue;
			}

			// Substitute boolean variable with true/false
			if ( enode->isVar( ) )
			{
				substitutions[ enode ] = polarity ? egraph.mkTrue( ) : egraph.mkFalse( );
				// Save substitution for retrieving model
				egraph.addSubstitution( enode, substitutions[ enode ] );
				continue;
			}

			if ( polarity )
				constant_substs[ enode ] = egraph.mkTrue( );
			else
				constant_substs[ enode ] = egraph.mkFalse( );

			assert( false );
		}
	}

	// Done with cache
	egraph.doneDup1( );
	bool res = true;

	return res;
}

bool TopLevelProp::contains( Enode * term, Enode * var )
{
	vector< Enode * > unprocessed_enodes;
	egraph.initDup2( );

	unprocessed_enodes.push_back( term );
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		if ( enode == var )
		{
			egraph.doneDup2( );
			return true;
		}
		//
		// Skip if the node has already been processed before
		//
		if ( egraph.isDup2( enode ) )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( ) ;
				arg_list != egraph.enil ;
				arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );
			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( !egraph.isDup2( arg ) )
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
		egraph.storeDup2( enode );
	}

	egraph.doneDup2( );

	return false;
}

Enode * TopLevelProp::substitute( Enode * formula, map< Enode *, Enode * > & substitutions, bool & sub_stop )
{
	assert( formula );
	list< Enode * > reinsert_back;

	vector< Enode * > unprocessed_enodes;
	egraph.initDupMap1( );

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
		if ( egraph.valDupMap1( enode ) != NULL )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( )
				; arg_list != egraph.enil
				; arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );

			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( egraph.valDupMap1( arg ) == NULL )
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

		map< Enode *, Enode * >::iterator it = substitutions.find( enode );
		if ( enode->isVar( ) )
		{
			// Substitute
			if ( it != substitutions.end( ) )
				result = it->second;
		}

		if ( result == NULL )
			result = egraph.copyEnodeEtypeTermWithCache( enode );
		else
			sub_stop = false;

		assert( result );
		assert( egraph.valDupMap1( enode ) == NULL );
		egraph.storeDupMap1( enode, result );
	}

	Enode * new_formula = egraph.valDupMap1( formula );

	egraph.doneDupMap1( );
	assert( new_formula );
	return new_formula;
}


void TopLevelProp::computeIncomingEdges( Enode * formula, vector< int > & id_to_inc_edges )
{
	assert( formula );

	vector< Enode * > unprocessed_enodes;
	egraph.initDup1( );

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
		if ( egraph.isDup1( enode ) )
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
			if ( !egraph.isDup1( arg ) )
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

		for ( Enode * ll = enode->getCdr( )
				; !ll->isEnil( )
				; ll = ll->getCdr( ) )
		{
			Enode * arg = ll->getCar( );
			if ( arg->getId( ) >= (enodeid_t)id_to_inc_edges.size( ) )
				id_to_inc_edges.resize( arg->getId( ) + 1, 0 );
			id_to_inc_edges[ arg->getId( ) ] ++;
		}

		egraph.storeDup1( enode );
	}

	egraph.doneDup1( );
}
