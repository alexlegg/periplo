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
#include "Enode.h"
#include "SimpSATSolver.h"

using namespace periplo;

//
// Inform the solver about the existence of node e
//
lbool Egraph::inform( Enode * e )
{
	assert( e );
	assert( theoryInitialized );

#ifdef PRODUCE_PROOF
	assert( config.produce_inter == 0 || e->getIPartitions( ) != 0 );
#endif

	lbool status;
	map< enodeid_t, lbool >::iterator it = informed.find( e->getId( ) );

	if ( it == informed.end( ) )
	{
		if ( e->getId( ) >= (enodeid_t)id_to_belong_mask.size( ) )
			id_to_belong_mask.resize( e->getId( ) + 1, 0 );

		assert( id_to_belong_mask[ e->getId( ) ] == 0 );
		informed[ e->getId( ) ] = status;
	}
	else
	{
		status = it->second;
	}

	return status;
}

//
// Pushes a backtrack point
//
void Egraph::pushBacktrackPoint( )
{
	// Save solver state if required
	assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
	backtrack_points.push_back( undo_stack_term.size( ) );
}

//
// Pops a backtrack point
//
void Egraph::popBacktrackPoint( )
{
	assert( backtrack_points.size( ) > 0 );
	size_t undo_stack_new_size = backtrack_points.back( );
	backtrack_points.pop_back( );
	backtrackToStackSize( undo_stack_new_size );
}

void Egraph::initializeSolver( SimpSATSolver * s )
{
	setSolver( s );
	assert( !theoryInitialized );
	theoryInitialized = true;
	assert( config.logic == QF_BOOL );
}

void Egraph::computeModel( )
{
	model_computed = true;

	// Compute values for variables removed
	// during preprocessing, starting from
	// the last
	//
	for ( int i = top_level_substs.size( ) - 1 ; i >= 0 ; i -- )
	{
		Enode * var = top_level_substs[i].first;
		Enode * term = top_level_substs[i].second;
	}
}

void Egraph::printModel( ostream & os )
{
	assert( config.produce_models );
	computeModel( );
	//
	// Print values
	//
	for( set< Enode * >::iterator it = variables.begin( ); it != variables.end( ); it ++ )
	{
		// Retrieve enode
		Enode * v = *it;
		// Print depending on type
		if ( v->hasSortBool( ) ) continue;
		else periplo_error2( "model printing unsupported for this variable: ", v );
		os << endl;
	}
}

//
// Backtracks stack to a certain size
//
void Egraph::backtrackToStackSize ( size_t size )
{
	//
	// Restore state at previous backtrack point
	//
	while ( undo_stack_term.size( ) > size )
	{
		oper_t last_action = undo_stack_oper.back( );
		Enode * e = undo_stack_term.back( );

		undo_stack_oper.pop_back( );
		undo_stack_term.pop_back( );

		if ( last_action == SYMB )
			removeSymbol( e );
		else if ( last_action == INSERT_STORE )
			removeStore( e );
		else
			periplo_error( "unknown action" );
	}

	assert( undo_stack_term.size( ) == undo_stack_oper.size( ) );
}

bool Egraph::checkDupClause( Enode * c1, Enode * c2 )
{
	assert( c1 );
	assert( c2 );
	// Swap let cl3 be the lowest clause
	if ( c1->getId( ) > c2->getId( ) )
	{
		Enode * tmp = c1;
		c1 = c2;
		c2 = tmp;
	}

#ifdef BUILD_64
	enodeid_pair_t sig = encode( c1->getId( ), c2->getId( ) );
#else
	Pair( enodeid_t ) sig = make_pair( c1->getId( ), c2->getId( ) );
#endif

	const bool res = clauses_sent.insert( sig ).second == false;
	return res;
}


//
// Pushes a backtrack point
//
void Egraph::extPushBacktrackPoint( )
{
	// Save solver state if required
	assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
	backtrack_points.push_back( undo_stack_term.size( ) );
}

//
// Pops a backtrack point
//
void Egraph::extPopBacktrackPoint( )
{
	assert( backtrack_points.size( ) > 0 );
	size_t undo_stack_new_size = backtrack_points.back( );
	backtrack_points.pop_back( );
	backtrackToStackSize( undo_stack_new_size );
}
