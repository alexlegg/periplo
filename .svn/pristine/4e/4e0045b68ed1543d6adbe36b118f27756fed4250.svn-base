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


#include "CoreSATSolver.h"

#ifdef PRODUCE_PROOF
#include "Proof.h"
#include <sys/wait.h>
#endif

using namespace periplo;

void CoreSATSolver::dumpRndInter( )
{
	const char * name = "rnd_inter.smt2";
	std::ofstream dump_out( name );

	dump_out << "(set-logic QF_BOOL)" << endl;
	egraph.dumpHeaderToFile( dump_out );
	dump_out << "(set-option :produce-interpolants true)" << endl;

	int i_c = 0, i_t = 0;
	int step_c = clauses.size( )/(config.sat_dump_rnd_inter+1), limit_c = 0;
	int step_t = trail.size( )/(config.sat_dump_rnd_inter+1), limit_t = 0;
	//
	// Dump from first to last but one
	//
	for ( int part = 1 ; part <= config.sat_dump_rnd_inter ; part ++ )
	{
		limit_c += step_c;
		limit_t += step_t;
		dump_out << "; Partition " << part << endl;
		dump_out << "(assert" << endl;
		dump_out << "(and" << endl;

		for ( ; i_c < limit_c ; i_c ++ )
		{
			Clause & c = ca [ clauses[ i_c ] ];

			if ( c.mark( ) == 1 ) continue;

			printClause( dump_out, c );
			dump_out << endl;
		}
		//
		// Also dump the trail which contains clauses of size 1
		//
		for ( ; i_t < limit_t ; i_t ++ )
		{
			Var v = var(trail[i_t]);
			if ( v <= 1 ) continue;
			Enode * e = enode_handler->varToEnode( v );
			dump_out << (sign(trail[i_t])?"(not ":" ") << e << (sign(trail[i_t])?") ":" ") << endl;
		}
		dump_out << "))" << endl;
	}
	//
	// Dump last
	//
	dump_out << "; Partition " << config.sat_dump_rnd_inter + 1 << endl;
	dump_out << "(assert" << endl;
	dump_out << "(and" << endl;

	for ( ; i_c < clauses.size( ) ; i_c ++ )
	{
		Clause & c = ca [ clauses[ i_c ] ];

		if ( c.mark( ) == 1 ) continue;

		printClause( dump_out, c );
		dump_out << endl;
	}
	//
	// Also dump the trail which contains clauses of size 1
	//
	for ( ; i_t < trail.size( ) ; i_t ++ )
	{
		Var v = var(trail[i_t]);
		if ( v <= 1 ) continue;
		Enode * e = enode_handler->varToEnode( v );
		dump_out << (sign(trail[i_t])?"(not ":" ") << e << (sign(trail[i_t])?") ":" ") << endl;
	}
	dump_out << "))" << endl;
	//
	// Add Check sat
	//
	dump_out << "(check-sat)" << endl;
	dump_out << "(get-interpolants)" << endl;
	dump_out << "(exit)" << endl;

	dump_out.close( );
	cerr << "[Dumped " << name << "]" << endl;
	exit( 0 );
}

#ifdef PRODUCE_PROOF

Proof::Proof( ClauseAllocator& cl )
: begun     ( false )
, chain_cla ( NULL )
, chain_var ( NULL )
, last_added( CRef_Undef )
, cl_al		( cl )
{ }

Proof::~Proof( )
{
	if(chain_var) delete chain_var;
	if(chain_cla) delete chain_cla;
	for( map< CRef, ProofDer * >::iterator it = clause_to_proof_der.begin(); it != clause_to_proof_der.end(); it++ )
	{
		ProofDer* pd = it->second;
		if(pd) delete pd;
	}
}

//
// Allocates the necessary structures to track
// the derivation of this clause c
//
void Proof::addRoot( CRef c, clause_type_t t )
{
	//cerr << "Adding root " << c << endl;
	assert( c != CRef_Undef );
	assert( notBegun( ) );
	assert( t == CLA_ORIG || t == CLA_LEARNT );
	// Do nothing. Just complies with previous interface
	ProofDer * d = new ProofDer( );
	d->chain_cla = new vector< CRef >;
	d->chain_var = new vector< Var >;
	// Not yet referenced
	d->ref = 0;
	d->type = t;
	assert( clause_to_proof_der.find( c ) == clause_to_proof_der.end( ) );
	clause_to_proof_der[ c ] = d;
	last_added = c;
}

//
// This is the beginning of a derivation chain.
//
void Proof::beginChain( CRef c )
{
	//cerr << "Beginning chain " << c << endl;
	assert( c != CRef_Undef );
	assert( notBegun( ) );
	begun = true;
	assert( chain_cla == NULL );
	assert( chain_var == NULL );
	// Allocates the temporary store for the chain of clauses and variables
	chain_cla = new vector< CRef >;
	chain_var = new vector< Var >;
	// Sets the first clause of the chain
	chain_cla->push_back( c );
	assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
	// Increase reference
	clause_to_proof_der[ c ]->ref ++;
}

//
// Store a resolution step with chain_cla.back( ) and c 
// on the pivot variable p
//
void Proof::resolve( CRef c, Var p )
{
	//cerr << "Resolving" << endl;
	assert( c != CRef_Undef );
	chain_cla->push_back( c );
	chain_var->push_back( p );
	assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
	// Increase reference
	clause_to_proof_der[ c ]->ref ++;
}

//
// This is called when we need to throw away the
// temporary chains of resolution steps accumulated
// for the last clause
//
void Proof::endChain( )
{
	assert( begun );
	begun = false;
	assert( chain_cla );
	assert( chain_var );
	delete chain_cla;
	delete chain_var;
	chain_var = NULL;
	chain_cla = NULL;
}

//
// Finalize the temporary chain
// NULL is the empty clause 
//
void Proof::endChain( CRef res )
{
	//cerr << "Ending chain " << res << endl;
	assert( begun );
	begun = false;
	// Chains of size 1 are not admissible in propositional logic
	if( chain_cla->size() <= 1 ) periplo_error2("Found chain of size ",chain_cla->size());
	// Save the temporary derivation chain in a new derivation structure
	ProofDer * d = new ProofDer( );
	assert( chain_cla );
	assert( chain_var );
	d->chain_cla = chain_cla;
	d->chain_var = chain_var;
	d->type = CLA_LEARNT;
	d->ref = 0;
	assert( clause_to_proof_der.find( res ) == clause_to_proof_der.end( ) );
	// Create association between res and its derivation chain
	clause_to_proof_der[ res ] = d;
	last_added = res;
	chain_cla = NULL;
	chain_var = NULL;
}

bool Proof::deletable( CRef c )
{
	//cerr << "Trying to delete " << c << endl;
	// Never remove units
	if ( cl_al[c].size( ) == 1 ) return false;
	assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
	ProofDer * d = clause_to_proof_der[ c ];
	assert( d );
	assert( d->ref >= 0 );
	// This clause is still used somewhere else, keep it
	if ( d->ref > 0 ) return false;
	// Dereference parents
	for ( unsigned i = 0 ; i < d->chain_cla->size( ) ; i ++ )
	{
		// Dereference of one
		if( clause_to_proof_der.find( (*(d->chain_cla))[i] ) == clause_to_proof_der.end( ) )
			continue;
		ProofDer * dc = clause_to_proof_der[ (*(d->chain_cla))[i] ];
		dc->ref --;
	}
	assert( d->ref == 0 );
	// Remove derivation
	delete d;
	// Remove correspondence
	clause_to_proof_der.erase( c );
	// Can be removed
	cl_al.free( c );
	//cerr << "Deleting " << c << endl;
	return true;
}

void Proof::forceDelete( CRef c )
{
	//cerr << "Forcing deletion of " << c << endl;
	assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
	ProofDer * d = clause_to_proof_der[ c ];
	assert( d );
	delete d;
	clause_to_proof_der.erase( c );
	cl_al.free( c );
}

void Proof::printCurrChain()
{
	if( chain_cla == NULL || chain_var == NULL ) return;
	assert((*chain_cla).size() == (*chain_var).size() + 1);
	cerr << "First clause: ";
	Clause& c = cl_al[ (*chain_cla)[0] ];
	for (int j = 0; j < c.size(); j++){
		Lit l = c[j];
		reportf("%s%-3d", sign(l) ? "-" : "", var(l) );
		cerr << " ";
	}
	cerr << endl;

	for( int i = 1; i < (*chain_var).size(); i ++ )
	{
		cerr << "Clause: ";
		Clause& c = cl_al[ (*chain_cla)[i] ];
		for (int j = 0; j < c.size(); j++){
			Lit l = c[j];
			reportf("%s%-3d", sign(l) ? "-" : "", var(l) );
			cerr << " ";
		}
		cerr << "\t\t Pivot: " << (*chain_var)[i-1]  << endl;
	}
}

// TODO to be implemented
void Proof::pushBacktrackPoint( ){}
void Proof::popBacktrackPoint( ){}
void Proof::reset( ){}

void Proof::print( ostream & out, CoreSATSolver & s, EnodeHandler & t )
{
	if ( clause_to_proof_der.find( CRef_Undef ) == clause_to_proof_der.end( ) )
		periplo_error( "there is no proof of false" );

	out << "(proof " << endl;

	int nof_lets = 0;

	vector< CRef > unprocessed;
	unprocessed.push_back( CRef_Undef );
	set< CRef > cache;
	set< CRef > core;

	while( !unprocessed.empty( ) )
	{
		CRef c = unprocessed.back( );
		// Skip already seen
		if ( cache.find( c ) != cache.end( ) )
		{
			unprocessed.pop_back( );
			continue;
		}
		assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
		ProofDer * d = clause_to_proof_der[ c ];

		// Special case in which there is not
		// a derivation but just an equivalence
		if ( d->chain_cla->size( ) == 1 )
		{
			// Say c is done
			cache.insert( c );
			// Move to equiv
			c = (*d->chain_cla)[0];
			// Retrieve derivation
			assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
			d = clause_to_proof_der[ c ];
		}
		assert( d->chain_cla->size( ) != 1 );
		// Look for unprocessed children
		bool unproc_children = false;
		for ( unsigned i = 0 ; i < d->chain_cla->size( ) ; i ++ )
		{
			CRef cc = (*(d->chain_cla))[i];
			if ( cache.find( cc ) == cache.end( ) )
			{
				unproc_children = true;
				unprocessed.push_back( cc );
			}
		}
		// Depth first
		if ( unproc_children ) continue;
		// Remove current
		unprocessed.pop_back( );

		if ( d->chain_cla->size( ) > 0 )
		{
			out << "; ";
			if ( c == CRef_Undef )
				out << "-";
			else
				s.printClause( out, c );
			out << endl;
			out << "(let (cls_" << c;
			nof_lets ++;

			vector< CRef > & chain_cla = (*(d->chain_cla));
			vector< Var > & chain_var = (*(d->chain_var));

			assert( chain_cla.size( ) == chain_var.size( ) + 1 );

			for ( unsigned i = 1 ; i < chain_cla.size( ) ; i ++ )
				out << " (res";
			for ( unsigned ic = 1, iv = 0 ; iv < chain_var.size( ) ; ic ++, iv ++ )
			{
				if ( ic == 1 )
				{
					assert( iv == 0 );
					out << " cls_" << chain_cla[ 0 ]
					                             << " cls_" << chain_cla[ 1 ]
					                                                      << " " << t.varToEnode( chain_var[ 0 ] )
					                                                      << ")";
				}
				else
				{
					out << " cls_" << chain_cla[ ic ]
					                             << " " << t.varToEnode( chain_var[ iv ] )
					                             << ")";
				}
			}
			out << ")" << endl;
		}
		else
		{
			if ( d->type == CLA_ORIG ) core.insert( c );
			out << "(let (cls_" << c << " ";
			s.printClause( out, c );
			out << ")" << endl;
			nof_lets ++;
		}
		cache.insert( c );
	}
	out << "cls_0"  << endl;

	for ( int i = 0 ; i < nof_lets ; i ++ ) out << ")";
	out << endl;

	out << ":core" << endl;
	out << "( ";
	for ( set< CRef >::iterator it = core.begin( ); it != core.end( ); it ++ )
	{
		out << "cls_" << *it << " ";
	}
	out << ")" << endl;
	out << ")" << endl;
}

//=============================================================================
// The following functions are declared in CoreSATSolver.h

void CoreSATSolver::createProofGraph ()
{ proof_graph = new ProofGraph( config, *this, enode_handler, egraph, proof, nVars( ) ); }

void CoreSATSolver::deleteProofGraph () { delete proof_graph; }

void CoreSATSolver::printProofSMT2( ostream & out )
{ proof.print( out, *this, *enode_handler ); }

void CoreSATSolver::printProofDotty( )
{ assert(proof_graph); proof_graph->printProofGraph(); }

void CoreSATSolver::printInter( ostream & out )
{
	assert( config.produce_inter != 0 );

	if( config.print_proofs_smtlib2 > 0 ) proof.print( out, *this, *enode_handler );

	// Compute interpolants
	vector< Enode * > sequence_of_interpolants;
	assert(proof_graph);
	if( config.proof_multiple_inter == 0)
		proof_graph->producePathInterpolants( sequence_of_interpolants );
	else if( config.proof_multiple_inter == 1)
		proof_graph->produceSimultaneousAbstraction( sequence_of_interpolants );
	else if( config.proof_multiple_inter == 2)
		proof_graph->produceGenSimultaneousAbstraction( sequence_of_interpolants );
	else if( config.proof_multiple_inter == 3)
		proof_graph->produceStateTransitionInterpolants( sequence_of_interpolants );
	else
		periplo_error( "Please choose a value between 0 and 3" );


	for( size_t i = 0 ; i < sequence_of_interpolants.size( ) ; i ++ )
	{
		// Before printing, we have to undo definitions
		// for instance those introduced when converting
		// to CNF or when replacing ITEs
		Enode * interp = sequence_of_interpolants[ i ];
		interp = egraph.maximize( interp );
		interp = egraph.expandDefinitions( interp );

		// FIXME restore proper printing whenever necessary
		out << "; Interpolant " << i << endl;
		//out << interp << endl; // More clear, less efficient
		egraph.dumpFormulaToFile( out, interp ); // More efficient, thanks to let and ?def
		// Save again
		sequence_of_interpolants[ i ] = interp;
	}
}

// Create interpolants with each A consisting of the specified partitions
void CoreSATSolver::getInterpolants(const vector<vector<int> >& partitions, vector<Enode*>& interpolants)
{ assert(proof_graph); proof_graph->produceConfigMatrixInterpolants( partitions, interpolants ); }

#ifdef FULL_LABELING
void CoreSATSolver::setColoringSuggestions	( vector< std::map<Enode*, icolor_t>* > * mp ){ proof_graph->setColoringSuggestions(mp); }
#endif

void CoreSATSolver::getSingleInterpolant(vector<Enode*>& interpolants)
{ assert(proof_graph); proof_graph->produceSingleInterpolant(interpolants); }

bool   CoreSATSolver::getPathInterpolants(vector<Enode*>& interpolants)
{ assert(proof_graph); return proof_graph->producePathInterpolants( interpolants ); }

bool   CoreSATSolver::getSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants)
{ assert(proof_graph); return proof_graph->produceSimultaneousAbstraction( interpolants ); }

bool   CoreSATSolver::getGenSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants)
{ assert(proof_graph); return proof_graph->produceGenSimultaneousAbstraction( interpolants ); }

bool   CoreSATSolver::getStateTransitionInterpolants(vector<Enode*>& interpolants)
{ assert(proof_graph); return proof_graph->produceStateTransitionInterpolants( interpolants ); }

bool   CoreSATSolver::getTreeInterpolants(InterpolationTree* it, vector<Enode*>& interpolants)
{ assert(proof_graph); return proof_graph->produceTreeInterpolants( it, interpolants ); }

void CoreSATSolver::reduceProofGraph()
{ assert(proof_graph); proof_graph->transfProofForReduction( ); }

bool CoreSATSolver::checkImplication( Enode* f1, Enode* f2 )
{
	if( config.verbosity > 0 ) { cerr << "# Checking implication phi_1 -> phi_2" << endl; }
	// First stage: print declarations
	const char * name = "verifyimplication.smt2";
	ofstream dump_out( name );
	egraph.dumpHeaderToFile( dump_out );
	// Add first formula
	egraph.dumpFormulaToFile( dump_out, f1, false );
	// Add negation second formula
	egraph.dumpFormulaToFile( dump_out, f2, true );
	dump_out << "(check-sat)" << endl;
	dump_out << "(exit)" << endl;
	dump_out.close( );

	// Check !
	bool impl_holds = true;
	bool tool_res;
	if ( int pid = fork() )
	{
		int status;
		waitpid(pid, &status, 0);
		switch ( WEXITSTATUS( status ) )
		{
		case 0:
			tool_res = false;
			break;
		case 1:
			tool_res = true;
			break;
		default:
			perror( "# Error: Certifying solver returned weird answer (should be 0 or 1)" );
			exit( EXIT_FAILURE );
		}
	}
	else
	{
		execlp( config.certifying_solver, config.certifying_solver, name, NULL );
		perror( "Error: Certifying solver had some problems (check that it is reachable and executable)" );
		exit( EXIT_FAILURE );
	}
	remove(name);
	if ( tool_res == true )
	{
		cerr << "External tool says phi_1 -> phi_2 does not hold" << endl;
		impl_holds = false;
	}
	else
	{
		cerr << "External tool says phi_1 -> phi_2 holds" << endl;
	}
	return impl_holds;
}
#endif
