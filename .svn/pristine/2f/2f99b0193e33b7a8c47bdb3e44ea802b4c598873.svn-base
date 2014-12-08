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

#include "EnodeHandler.h"
#include "SimpSATSolver.h"
#include <sys/wait.h>

using namespace periplo;

//
// Return the MiniSAT Variable corresponding to
// the positive input enode. Creates the correspondence
// by adding a new MiniSAT variable, if it doesn't exists
//
Var EnodeHandler::enodeToVar( Enode * atm )
{
	assert( atm );
	assert( atm->isAtom( ) );
	assert( !atm->isTrue( ) );
	assert( !atm->isFalse( ) );

	if ( enode_id_to_var.size( ) <= (unsigned)atm->getId( ) )
		enode_id_to_var.resize( atm->getId( ) + 1, var_Undef );

	Var v = enode_id_to_var[ atm->getId( ) ];
	if ( v == var_Undef )
	{
			// There is no variable in MiniSAT for this enode
			// Create a new variable and store the correspondence
			v = solver.newVar( ); // Default polarity
			enode_id_to_var[ atm->getId( ) ] = v;
			if ( var_to_enode.size( ) <= (unsigned)v ) var_to_enode.resize( v + 1, NULL );
			assert( var_to_enode[ v ] == NULL );
			var_to_enode[ v ] = atm;
	}
	assert( v != var_Undef );
	return v;
}

//
// Return the MiniSAT literal corresponding to
// the input enode literal. Creates the correspondence
// by adding a new MiniSAT variable, if it doesn't exists
//
Lit EnodeHandler::enodeToLit( Enode * elit )
{
	assert( elit );
	assert( elit->isLit( ) );

	bool negated = elit->isNot( );
	Enode * atm = negated ? elit->getCdr( )->getCar( ) : elit;
	Var v = enodeToVar( atm );
	return mkLit( v, negated );
}

Enode * EnodeHandler::varToEnode( Var v )
{
	assert( v < (int)var_to_enode.size( ) );
	assert( var_to_enode[ v ] != NULL );
	return var_to_enode[ v ];
}

void EnodeHandler::clearVar( Var v )
{
	assert( var_to_enode[ v ] != NULL );
	Enode * e = var_to_enode[ v ];
	assert( e->getId( ) < static_cast< int >( enode_id_to_var.size( ) ) );
	assert( enode_id_to_var[ e->getId( ) ] == v );
	var_to_enode[ v ] = NULL;
	enode_id_to_var[ e->getId( ) ] = var_Undef;
}
