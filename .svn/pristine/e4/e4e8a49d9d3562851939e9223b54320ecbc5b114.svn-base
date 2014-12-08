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
#define PRODUCE_PROOF

#include "PeriploContext.h"
#include "TopLevelProp.h"
#include <csignal>

namespace periplo {

bool stop;

}

using namespace periplo;

void PeriploContext::SetLogic( logic_t l )
{ 
	if ( l  == EMPTY ) config.logic = EMPTY;
	else if ( l == QF_BOOL ) config.logic = QF_BOOL;
	else periplo_error( "logic not supported " );
	egraph.initializeStore( );
	solver.initialize( );

	egraph.initializeSolver( &solver );
	init = true;
}

void PeriploContext::SetLogic( const char * str )
{
	if ( strcmp( str, "EMPTY" )     == 0 ) config.logic = EMPTY;
	else if ( strcmp( str, "QF_BOOL" )   == 0 ) config.logic = QF_BOOL;
	else periplo_error2( "logic not supported ", str );
	egraph.initializeStore( );
	solver.initialize( );
	init = true;
}

void PeriploContext::SetInfo( const char * key )
{
	periplo_error2( "command not supported (yet)", key );
}

void PeriploContext::SetInfo( const char * key, const char * attr )
{
	assert( key );
	assert( attr );

	if ( strcmp( key, ":status" ) == 0 )
	{
		if ( strcmp( attr, "sat" ) == 0 )
			config.status = l_True;
		else if ( strcmp( attr, "unsat" ) == 0 )
			config.status = l_False;
		else if ( strcmp( attr, "unknown" ) == 0 )
			config.status = l_Undef;
		else
			periplo_error2( "unrecognized attribute", attr );
	}
	else if ( strcmp( key, ":smt-lib-version" ) == 0 )
		; // Do nothing
	else if ( strcmp( key, ":category" ) == 0 )
		; // Do nothing
	else if ( strcmp( key, ":source" ) == 0 )
		; // Do nothing
	else
		periplo_error2( "unrecognized key", key );
}

void PeriploContext::SetOption( const char * key )
{
	periplo_error2( "command not supported (yet)", key );
}

void PeriploContext::SetOption( const char * key, const char * attr )
{
	assert( key );
	assert( attr );

	if ( strcmp( key, ":print-success" ) == 0 )
	{
		if ( strcmp( attr, "true" ) == 0 )
			config.print_success = true;
	}
	else if ( strcmp( key, ":expand-definitions" ) == 0 )
		periplo_warning2( key, " not yet supported, skipping.")
		else if ( strcmp( key, ":interactive-mode" ) == 0 )
			periplo_warning2( key, " not yet supported, skipping.")
			else if ( strcmp( key, ":produce-unsat-cores" ) == 0 )
				periplo_warning2( key, " not yet supported, skipping.")
				else if ( strcmp( key, ":produce-models" ) == 0 )
					config.setProduceModels( );
				else if ( strcmp( key, ":produce-assignments" ) == 0 )
					periplo_warning2( key, " not yet supported, skipping.")
					else if ( strcmp( key, ":produce-interpolants" ) == 0 )
						config.setProduceInter( );
					else if ( strcmp( key, ":regular-output-channel" ) == 0 )
						config.setRegularOutputChannel( attr );
					else if ( strcmp( key, ":diagnostic-output-channel" ) == 0 )
						config.setDiagnosticOutputChannel( attr );
					else if ( strcmp( key, ":random-seed" ) == 0 )
						periplo_warning2( key, " not yet supported, skipping.")
						else if ( strcmp( key, ":verbosity" ) == 0 )
							config.verbosity = atoi( attr );
						else
							periplo_warning2( "skipping option ", key );
}


int PeriploContext::executeCommands( )
{
	assert( init );

	int ret_val = 0;

	// Weird situation
	if ( nof_checksat <= 0 )
	{
		periplo_warning(" no satisfiability checking done");
		return 2;
	}

	// Trick for efficiency
	if ( nof_checksat == 1 ) ret_val = executeStatic( );
	// Normal incremental solving
	else
	{
		periplo_error(" incremental solving not enabled (yet); please add only one satisfiability check command to the queue");
		//config.incremental = 1;
		//ret_val = executeIncremental( );
	}

	return ret_val;
}

/*int PeriploContext::executeIncremental( )
{
	assert( init );
	assert( config.incremental == 1 );

	// Initialize solver
	egraph.initializeSolver( &solver );

	lbool status = l_Undef;

	for ( size_t i = 0 ; i < command_list.size( ) ;  ++ i )
	{
		Command & c = command_list[ i ];

		// Commands blocked with assert( false ) are issued from parser directly
		switch( c.command )
		{
		case SET_LOGIC:
			assert( false );
			break;
		case SET_OPTION:
			assert( false );
			break;
		case SET_INFO:
			assert( false );
			break;
		case DECLARE_SORT:
			DeclareSort( c.str, c.num );
			break;
		case DEFINE_SORT:
			periplo_error( "construct define-sort not yet supported" );
			break;
		case DECLARE_FUN:
			DeclareFun( c.str, c.sort_arg, c.sort_ret );
			break;
		case DEFINE_FUN:
			periplo_error( "construct define-fun not yet supported" );
			break;
		case PUSH:
			Push( );
			break;
		case POP:
			Pop( );
			break;
		case ASSERT:
			Assert( c.enode );
			break;
		case CHECK_SAT:
			status = CheckSAT( );
			break;
		case GET_ASSERTIONS:
			periplo_error( "construct get-assertions not yet supported" );
			break;
		case GET_PROOF:
			GetProof( );
			break;
		case GET_INTERPOLANTS:
			GetInterpolants( );
			break;
		case GET_UNSAT_CORE:
			periplo_error( "construct get-unsat-core not yet supported" );
			break;
		case GET_VALUE:
			periplo_error( "construct get-value not yet supported" );
			break;
		case GET_ASSIGNMENT:
			periplo_error( "construct get-assignment not yet supported" );
			break;
		case GET_OPTION:
			periplo_error( "construct get-option not yet supported" );
			break;
		case GET_INFO:
			periplo_error( "construct get-info not yet supported" );
			break;
		case EXIT:
			Exit( );
			break;
		default:
			periplo_error( "case not handled" );
		}
	}
	return 0;
}*/

//
// Execute a script in which there is only
// one check-sat. We can use specialized
// functions, such as preprocessing, to
// improve performance
//
int PeriploContext::executeStatic( )
{
	assert( init );
	//assert( config.incremental == 0 );
	//
	// Hack for SMT-COMP 2010 for retrieving formula
	//
	for ( size_t i = 0 ; i < command_list.size( ) ; i ++ )
	{
		Command & c = command_list[ i ];
		if ( c.command == ASSERT ) Assert( c.enode );
		else if ( c.command == CHECK_SAT )
			CheckSATStatic( );
		else if ( c.command == EXIT )
			Exit( );
		else if ( c.command == GET_PROOF )
			GetProof( );
		else if ( c.command == GET_INTERPOLANTS )
			GetInterpolants( );
		else
			periplo_error( "command not supported (yet)" );
	}
	return 0;
}

#ifdef PRODUCE_PROOF
void PeriploContext::CheckSATIncrementalForInterpolation( )
{
	if ( config.logic == UNDEF ) periplo_error( "unable to determine logic" );
	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Incrementally Checking" << endl;
	assert( config.produce_inter != 0 );

	// Top-Level Propagator.
	TopLevelProp propagator( egraph, config );

	// Initialize solver at the first partition
	if( next_partition == 1 ) egraph.initializeSolver( &solver );

	// Gather partitions
	for ( ;; )
	{
		// Get partition
		Enode * formula = egraph.getNextAssertion( );
		if ( formula == NULL ) break;
		formula = propagator.doit( formula );

		if ( config.dump_formula != 0 )
		{
			char buf[ 32 ];
			sprintf( buf, "presolve_%ld.smt2", next_partition );
			egraph.dumpToFile( buf, formula );
		}

		ipartitions_t partition = 0;
		// Set next partition index
		setbit( partition, next_partition ); next_partition++;
		// CNFize the input formula and feed clauses to the solver
		state = cnfizer.cnfizeAndGiveToSolver( formula, partition );
	}

	// Solve
	if ( state == l_Undef )
	{
		if ( config.sat_preprocess_booleans != 0 ) periplo_warning( "not using preprocessing with interpolation" );
		bool status = solver.satSolve( false );
		if( status ) state = l_True; else state = l_False;
	}

	// If computation has been stopped, return undef
	if ( periplo::stop ) state = l_Undef;
}
#endif

void PeriploContext::CheckSATStatic( )
{
#ifdef PRODUCE_PROOF
	if ( config.produce_inter != 0 )
		staticCheckSATInterp( );
	else
#endif
		staticCheckSATNointerp( );
}

#ifdef PRODUCE_PROOF
void PeriploContext::staticCheckSATInterp( )
{
	if ( config.logic == UNDEF ) periplo_error( "unable to determine logic" );
	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Statically Checking" << endl;
	assert( config.produce_inter != 0 );

	// Gather partitions
	vector< Enode * > assertions;
	for ( ;; )
	{
		// Get partition
		Enode * formula = egraph.getNextAssertion( );
		if ( formula == NULL ) break;
		assertions.push_back( formula );
	}

	// Top-Level Propagator.
	TopLevelProp propagator( egraph, config );

	// Initialize solver
	egraph.initializeSolver( &solver );

	for ( size_t in = 0 ; in < assertions.size( ) ; in ++ )
	{
		// Get formula
		Enode * formula = assertions[ in ];
		assert( in != 0 || formula != NULL );
		// Canonize atoms
		formula = propagator.doit( formula );

		if ( config.dump_formula != 0 )
		{
			char buf[ 32 ];
			sprintf( buf, "presolve_%ld.smt2", next_partition );
			egraph.dumpToFile( buf, formula );
		}

		ipartitions_t partition = 0;
		// Set next partition index
		setbit( partition, next_partition ); next_partition++;
		// CNFize the input formula and feed clauses to the solver
		state = cnfizer.cnfizeAndGiveToSolver( formula, partition );
	}

	// Solve
	if ( state == l_Undef )
	{
		if ( config.sat_preprocess_booleans != 0 ) periplo_warning( "not using preprocessing with interpolation" );
		bool status = solver.satSolve( false );
		if( status ) state = l_True; else state = l_False;
	}

	// If computation has been stopped, return undef
	if ( periplo::stop ) state = l_Undef;
}
#endif

void PeriploContext::staticCheckSATNointerp( )
{
	if ( config.logic == UNDEF ) periplo_error( "unable to determine logic" );
	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Statically Checking" << endl;
	assert( config.produce_inter == 0 );

	// Retrieve the formula
	Enode * formula = egraph.getUncheckedAssertions( );
	if ( config.dump_formula != 0 ) egraph.dumpToFile( "original.smt2", formula );
	if ( formula == NULL ) periplo_error( "formula undefined" );

	// Top-Level Propagator.
	TopLevelProp propagator( egraph, config );

	// Only if sat_dump_rnd_inter is not set
	if ( config.sat_dump_rnd_inter == 0 ) formula = propagator.doit( formula );
	if ( config.dump_formula != 0 ) egraph.dumpToFile( "propagated.smt2", formula );

	// Solve only if not simplified already
	if ( formula->isTrue( ) ) state = l_True;
	else if ( formula->isFalse( ) ) state = l_False;
	else
	{
		// Initialize solver
		egraph.initializeSolver( &solver );

		// Compute polarities
		egraph.computePolarities( formula );

		// CNFize the input formula and feed clauses to the solver
		state = cnfizer.cnfizeAndGiveToSolver( formula );

		// Solve
		if ( state == l_Undef )
		{
			bool status = solver.satSolve( config.sat_preprocess_booleans != 0 );
			if(status) state = l_True; else state = l_False;
		}

		// If computation has been stopped, return undef
		if ( periplo::stop ) state = l_Undef;
	}
}

lbool PeriploContext::CheckSAT( )
{
	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Checking satisfiability" << endl;

	// Retrieve the conjunction of the yet unchecked assertions
	Enode * formula = egraph.getUncheckedAssertions( );

	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Processing: " << formula << endl;

	state = cnfizer.cnfizeAndGiveToSolver( formula );
	if ( state == l_Undef )
	{
		bool status = solver.solve( );
		if(status) state = l_True; else state = l_False;
	}

	if ( config.print_success )
	{
		ostream & out = config.getRegularOut( );
		if ( state == l_Undef )
			out << "# UNKNOWN" << endl;
		else if ( state == l_False )
			out << "# UNSAT" << endl;
		else
			out << "# SAT" << endl;
	}

	return state;
}

lbool PeriploContext::CheckSAT( vec< Enode * > & assumptions )
{
	if ( config.verbosity > 1 )
		cerr << "# PeriploContext::Checking satisfiability" << endl;

	// Retrieve the conjunction of the yet unchecked assertions
	Enode * formula = egraph.getUncheckedAssertions( );

	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Processing: " << formula << endl;

	state = cnfizer.cnfizeAndGiveToSolver( formula );

	if ( state == l_Undef )
	{
		bool status = solver.solve( assumptions, false );
		if(status) state = l_True; else state = l_False;
	}

	if ( config.print_success )
	{
		ostream & out = config.getRegularOut( );
		if ( state == l_Undef )
			out << "# UNKNOWN" << endl;
		else if ( state == l_False )
			out << "# UNSAT" << endl;
		else
			out << "# SAT" << endl;
	}

	return state;
}

lbool PeriploContext::CheckSAT( vec< Enode * > & assumptions, unsigned limit )
{
	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Checking satisfiability" << endl;

	// Retrieve the conjunction of the yet unchecked assertions
	Enode * formula = egraph.getUncheckedAssertions( );

	if ( config.verbosity > 1 ) cerr << "# PeriploContext::Processing: " << formula << endl;

	state = cnfizer.cnfizeAndGiveToSolver( formula );
	if ( state == l_Undef )
	{
		bool status = solver.solve( assumptions, limit, false );
		if(status) state = l_True; else state = l_False;
	}

	if ( config.print_success )
	{
		ostream & out = config.getRegularOut( );
		if ( state == l_Undef )
			out << "# UNKNOWN" << endl;
		else if ( state == l_False )
			out << "# UNSAT" << endl;
		else
			out << "# SAT" << endl;
	}

	return state;
}





// =======================================================================
// Functions that actually execute actions

void PeriploContext::DeclareSort( const char * name, int arity )
{
	if ( config.verbosity > 1 )
		cerr << "# PeriploContext::Declaring sort "
		<< name
		<< " of arity "
		<< arity
		<< endl;

	sstore.newSymbol( name );
}

void PeriploContext::DeclareFun( const char * name, Snode * args, Snode * rets )
{
	if ( config.verbosity > 1 )
	{
		cerr << "# PeriploContext::Declaring function "
				<< name
				<< " of sort ";
		if ( args ) cerr << args;
		else cerr << "()";
		cerr << " " << rets << endl;
	}
	egraph.newSymbol( name, args, rets );
}

void PeriploContext::Push( )
{ 
	if ( config.verbosity > 1 )
		cerr << "# PeriploContext::Pushing backtrack point" << endl;

	solver.pushBacktrackPoint( );
}

void PeriploContext::Pop( )
{
	if ( config.verbosity > 1 )
		cerr << "# PeriploContext::Popping backtrack point" << endl;

	solver.popBacktrackPoint( );
}

void PeriploContext::Reset( )
{
	if ( config.verbosity > 1 )
		cerr << "# PeriploContext::Resetting" << endl;

	solver.reset( );
}

void PeriploContext::Assert( Enode * e )
{
	if ( config.verbosity > 1 )
	{
		if ( e->isBooleanOperator( ) )
			cerr << "# PeriploContext::Asserting formula with id " << e->getId( ) << endl;
		else
			cerr << "# PeriploContext::Asserting formula " << e << endl;
	}

	// Move an assertion into the Egraph
	// They are stored and might be preprocessed
	// before entering the actual solver
	egraph.addAssertion( e );
}

void PeriploContext::GetProof( )
{
#ifdef PRODUCE_PROOF
	if ( state == l_False )
	{
		if( config.print_proofs_smtlib2 > 0 ) solver.printProofSMT2( config.getRegularOut( ) );
		createProofGraph();
		//solver.getProofGraph()->getGraphInfo();
		if( config.print_proofs_dotty > 0) solver.printProofDotty();
		if( config.proof_reduce > 0 ) reduceProofGraph();
		deleteProofGraph();
	}
	else
		periplo_warning( "Skipping command (get-proof) as formula is not unsat" );
#else
	periplo_warning( "Skipping command (get-proof): you need a version of periplo compiled with --enable-proof" );
#endif
}

void PeriploContext::GetInterpolants( )
{
#ifdef PRODUCE_PROOF
	if ( config.produce_inter == 0 )
	{
		periplo_warning( "Skipping command (get-interpolants) as interpolation is not enabled" );
	}
	else if ( state == l_False )
	{
		// NOTE Configure at pleasure
		createProofGraph();
		if(config.proof_reduce > 0) reduceProofGraph();
		solver.printInter( config.getRegularOut( ) );
		deleteProofGraph();
	}
	else
	{
		periplo_warning( "Skipping command (get-interpolants) as formula is not unsat" );
	}
#else
	periplo_warning( "Skipping command (get-interpolants): you need a version of periplo compiled with --enable-proof" );
#endif
}

#ifdef PRODUCE_PROOF
void PeriploContext::createProofGraph()
{
	solver.createProofGraph();
	// NOTE Free some memory used by MiniSAT and PeRIPLO
	solver.clearDataStructures();
}

void PeriploContext::deleteProofGraph()
{ solver.deleteProofGraph(); }

void PeriploContext::reduceProofGraph()
{ solver.reduceProofGraph(); }

#ifdef FULL_LABELING
void PeriploContext::setColoringSuggestions	(  vector< std::map<Enode*, icolor_t>* > * mp )
{ solver.setColoringSuggestions(mp); }
#endif

void PeriploContext::getSingleInterpolant(vector<Enode*>& interpolants)
{ solver.getSingleInterpolant(interpolants); }

void PeriploContext::getInterpolants(const vector<vector<int> >& partitions, vector<Enode*>& interpolants)
{ solver.getInterpolants(partitions, interpolants); }

bool PeriploContext::getPathInterpolants(vector<Enode*>& interpolants)
{ return solver.getPathInterpolants(interpolants); }

bool PeriploContext::getSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants)
{ return solver.getSimultaneousAbstractionInterpolants(interpolants); }

bool PeriploContext::getGenSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants)
{ return solver.getGenSimultaneousAbstractionInterpolants(interpolants); }

bool PeriploContext::getStateTransitionInterpolants(vector<Enode*>& interpolants)
{ return solver.getStateTransitionInterpolants(interpolants); }

bool PeriploContext::getTreeInterpolants(InterpolationTree* it, vector<Enode*>& interpolants)
{ return solver.getTreeInterpolants(it, interpolants);}

bool PeriploContext::checkImplication( Enode* f1, Enode* f2)
{ return solver.checkImplication( f1, f2 ); }
#endif


void PeriploContext::Exit( )
{ 
	PrintResult( state, config.status );
}

void PeriploContext::PrintResult( const lbool & result, const lbool & config_status )
{
	ostream & out = config.getRegularOut( );
	(void)config_status;
	fflush( stderr );
	(void)config_status;
	//
	// For testing purposes we return error if bug is found
	//
	if ( config_status != l_Undef
			&& result != l_Undef
			&& result != config_status )
		out << "error" << endl;
	else
		if ( result == l_True )
			out << "# SAT" << endl;
		else if ( result == l_False )
			out << "# UNSAT" << endl;
		else if ( result == l_Undef )
			out << "# UNKNOWN" << endl;
		else
			periplo_error( "unexpected result" );

	fflush( stdout );

	if ( config.verbosity )
	{
		//
		// Statistics
		//
		double   cpu_time = periplo::cpuTime();
		reportf( "#\n" );
		reportf( "# CPU Time used: %g s\n", cpu_time == 0 ? 0 : cpu_time );
		uint64_t mem_used = memUsed();
		reportf( "# Memory used: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
		reportf( "#\n" );
	}
}

// =======================================================================
// Functions that add commands to the list

void PeriploContext::addAssert( Enode * t )
{
	Command c;
	c.command = ASSERT;
	c.enode = t;
	command_list.push_back( c );
}

void PeriploContext::addCheckSAT( )
{
	Command c;
	c.command = CHECK_SAT;
	command_list.push_back( c );
	nof_checksat ++;
}

void PeriploContext::addPush( int n )
{
	assert( n > 0 );
	for ( int i = 0 ; i < n ; ++ i )
	{
		Command c;
		c.command = PUSH;
		command_list.push_back( c );
	}
}

void PeriploContext::addPop( int n )
{
	assert( n > 0 );
	for ( int i = 0 ; i < n ; ++ i )
	{
		Command c;
		c.command = POP;
		command_list.push_back( c );
	}
}

void PeriploContext::addExit( )
{
	Command c;
	c.command = EXIT;
	command_list.push_back( c );
}


void PeriploContext::addGetProof( )
{
	Command c;
	c.command = GET_PROOF;
	command_list.push_back( c );
}

void PeriploContext::addGetInterpolants( )
{
	Command c;
	c.command = GET_INTERPOLANTS;
	command_list.push_back( c );
}

