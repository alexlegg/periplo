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

#ifndef PROOF2_H
#define PROOF2_H

#include "Global.h"
#include "CoreSATSolver.h"
#include "EnodeHandler.h"
#include "SolverTypes.h"

using periplo::minisat::CRef;
using periplo::minisat::Var;
using periplo::minisat::ClauseAllocator;
using periplo::minisat::Clause;

namespace periplo {
class CoreSATSolver;
class EnodeHandler;
}

namespace periplo {

//=================================================================================================

typedef enum { CLA_ORIG, CLA_LEARNT } clause_type_t;

struct ProofDer
{
	ProofDer( )
	: chain_cla ( NULL )
	, chain_var ( NULL )
	, ref       ( 0 )
	{ }

	~ProofDer( )
	{
		assert( chain_cla );
		delete chain_cla;
		if ( chain_var ) delete chain_var;
	}

	vector< CRef >* 	 chain_cla;               // Clauses chain
	vector< Var > *      chain_var;               // Pivot chain
	int                  ref;                     // Reference counter
	clause_type_t        type;                    // Type of the clause
};

class Proof 
{
	bool begun;					// For debugging

	vector< CRef > *            chain_cla;
	vector< Var > *             chain_var;
	map< CRef, ProofDer * > 	clause_to_proof_der;
	CRef                    	last_added;
	ClauseAllocator&			cl_al;

public:

	Proof ( ClauseAllocator& cl );
	~Proof( );

	void addRoot    ( CRef, clause_type_t );              // Adds a new root clause
	void beginChain ( CRef );                             // Beginning of resolution chain
	void resolve    ( CRef, Var );                        // Resolve
	void endChain   ( );                                      // Chain that ended in sat
	void endChain   ( CRef );                             // Last chain refers to clause
	bool deletable    ( CRef );                             // Check whether clause can be removed
	void forceDelete( CRef );         					// Remove unconditionally
	inline Clause& getClause	( CRef cr ) { return cl_al[cr]; } // Get clause from reference

	// TODO to be restored
	void pushBacktrackPoint     ( );                          // Restore previous state
	void popBacktrackPoint      ( );                          // Restore previous state
	void reset                    ( );                          // Reset proof data structures

	inline CRef last        ( ) { return last_added; }    // Return last clause added

	inline bool     notBegun  ( ) { return !begun; }        // Stupid check

	void print( ostream &, CoreSATSolver &, EnodeHandler & );     // Print proof in SMT-LIB format
	void printCurrChain();										// Prints the proof chain being built

	map< CRef, ProofDer * > & getProof( ) { return clause_to_proof_der; }
};
}

//=================================================================================================

#endif
