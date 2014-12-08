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

#ifndef PERIPLO_CONTEXT_H
#define PERIPLO_CONTEXT_H

#include "Egraph.h"
#include "SimpSATSolver.h"
#include "Tseitin.h"
#include "Global.h"

namespace periplo {

class PeriploContext
{
public:
	//
	// For scripts
	//
	PeriploContext( int    argc, char * argv[ ] )
: config_p     ( new SATConfig( argc, argv ) )
, config       ( *config_p )
, sstore_p     ( new SStore( config ) )
, sstore       ( *sstore_p )
, egraph_p     ( new Egraph( config, sstore ) )
, egraph       ( *egraph_p )
, solver_p     ( new SimpSATSolver( egraph, config ) )
, solver       ( *solver_p )
, cnfizer_p    ( new Tseitin( egraph, solver, config, sstore ) )
, cnfizer      ( *cnfizer_p )
, state        ( l_Undef )
, nof_checksat ( 0 )
, counter      ( 0 )
, init         ( false )
, next_partition ( 1 )
{ }
	//
	// For API library
	//
	PeriploContext( )
	: config_p     ( new SATConfig( ) )
	, config       ( *config_p )
	, sstore_p     ( new SStore( config ) )
	, sstore       ( *sstore_p )
	, egraph_p     ( new Egraph( config, sstore ) )
	, egraph       ( *egraph_p )
	, solver_p     ( new SimpSATSolver( egraph, config ) )
	, solver       ( *solver_p )
	, cnfizer_p    ( new Tseitin( egraph, solver, config, sstore ) )
	, cnfizer      ( *cnfizer_p )
	, state        ( l_Undef )
	, nof_checksat ( 0 )
	, counter      ( 0 )
	, init         ( false )
	, next_partition ( 1 )
	{
		config.incremental = 1;
	}

	~PeriploContext( )
	{
		assert( config_p );
		assert( sstore_p );
		assert( egraph_p );
		assert( solver_p );
		assert( cnfizer_p );
		delete cnfizer_p;
		delete solver_p;
		delete egraph_p;
		delete sstore_p;
		delete config_p;
	}

	//======================================================================
	//
	// Communication API
	//
	void          SetLogic	     	 ( logic_t );                        // Set logic
	void          SetLogic	     	 ( const char * );                   // Set logic
	void          SetOption            ( const char * );                   // Set option
	void          SetOption            ( const char *, const char * );     // Set option
	void          SetInfo              ( const char * );                   // Set info
	void          SetInfo              ( const char *, const char * );     // Set info
	void          DeclareSort          ( const char *, int );              // Declares a new sort
	void          DeclareFun           ( const char *, Snode *, Snode * ); // Declares a new function symbol

	void    	  Assert               ( Enode * );
	void          CheckSATStatic      ( );							   // Allow static checking after all formulae have been asserted
#ifdef PRODUCE_PROOF
	void 		   CheckSATIncrementalForInterpolation		( ); 		   // Allow incremental assertion and checking for interpolation
#endif
	inline lbool  getStatus    ( )           { return state; }
	void          Push                 ( );
	void          Pop                  ( );
	void          Reset                ( );
	void   		  Exit                 ( );
#ifdef PRODUCE_PROOF
	inline void	setVerbosity					 		( int verb ) { assert(verb>=0); config.verbosity = verb; }
	// Create the proof graph; must be called before generating the interpolants
	void 			createProofGraph						( );
	// Delete the proof graph
	void 			deleteProofGraph						( );

	// If set to 1 enables interpolants check
	// NOTE needs z3 and tool_wrapper.sh in the main directory
	inline void	setInterpolantCheck					 	( ) { config.proof_certify_inter = 1; }
	inline void	unsetInterpolantCheck					( ) { config.proof_certify_inter = 0; }

	// Generate collections of interpolants
	// If interpolants checks are enabled, the boolean flag returns whether the relevant property is satisfied
	void          	getInterpolants(const vector<vector<int> >& partitions, vector<Enode*>& interpolants);
	void            getSingleInterpolant(vector<Enode*>& interpolants);
	bool 			getPathInterpolants(vector<Enode*>& interpolants);
	bool 			getSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants);
	bool 			getGenSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants);
	bool 			getStateTransitionInterpolants(vector<Enode*>& interpolants);
	// InterpolationTree is defined in common/Global.h
	// NOTE The number of nodes N must be equal to the number of asserted formulae
	// Each node has a partition_id 1 <= i <= N corresponding to the i_th asserted formula
	// interpolants[j] returns the interpolant for node j+1
	bool			getTreeInterpolants(InterpolationTree*, vector<Enode*>& interpolants);

	// Set interpolation algorithm
	inline void   setMcMillanInterpolation                ( ) { config.proof_set_inter_algo = 0; }
	inline void   setPudlakInterpolation                  ( ) { config.proof_set_inter_algo = 1; }
	inline void   setMcMillanPrimeInterpolation           ( ) { config.proof_set_inter_algo = 2; }
#ifdef FULL_LABELING
	inline void   setMinimalInterpolation           	    ( ) { config.proof_set_inter_algo = 3; }
	void		    setColoringSuggestions					(  vector< std::map<Enode*, icolor_t>* > * );
	inline void   setColoringSuggestionsInterpolation      ( ) { config.proof_set_inter_algo = 4; }
#endif

	// Assume f1 and f2 are built on propositional variables already in the system
	// Return true if f1 => f2
	bool checkImplication( Enode* f1, Enode* f2);

	// For generation of individual interpolants (not sequences)
	// with McMillan, Pudlak, McMillan' algorithms
	// enable a fast application of A2 rules to the proof to make interpolants stronger or weaker
	void 		    enableRestructuringForStrongerInterpolant	    ( ) { config.proof_trans_strength = 1; }
	void 		    enableRestructuringForWeakerInterpolant	    	( ) { config.proof_trans_strength = 2; }
	void 		    disableRestructuringForStrongerWeakerInterpolant( ) { config.proof_trans_strength = 0; }

	// For AB pivots, instead of (I1 OR p) AND (I2 OR (NOT p)), use (I1 AND (NOT p)) OR (I2 AND p)
	inline void   setAlternativeInterpolation             ( ) { config.proof_alternative_inter = 1; }
	inline void   setStandardInterpolation           ( ) { config.proof_alternative_inter = 0; }

	// Reduce the proof graph
	void 			reduceProofGraph				( );
	inline void	enableRecyclePivots				( ) { config.proof_rec_piv = 1; }
	inline void	disableRecyclePivots			( ) { config.proof_rec_piv = 1; }
	inline void    enableUnitsPushDown				( ) { config.proof_push_units = 1; }
	inline void    disableUnitsPushDown		    ( ) { config.proof_push_units = 0; }
	inline void    enableTransfTraversals			( ) { config.proof_transf_trav = 1; }
	inline void    disableTransfTraversals		    ( ) { config.proof_transf_trav = 0; }
	inline void    enableStructHashing				( ) { config.proof_struct_hash = 1; }
	inline void    disableStructHashing		    ( ) { config.proof_struct_hash = 0; }
	// Enable structural hashing while building proof from proof chains
	inline void    enableStructHashingBuild		( ) { config.proof_struct_hash_build = 1; }
	inline void    disableStructHashingBuild		( ) { config.proof_struct_hash_build = 0; }
	// Inverts the default order Structural Hashing + RecyclePivots
	inline void	 switchToRPHashing				( )	{ config.proof_switch_to_rp_hash = 1; }
	inline void	 switchToHashingRP				( )	{ config.proof_switch_to_rp_hash = 0; }

	// If set to 1 enables proof check
	inline void	setProofCheck					 		( int c ) { assert(c>=0); config.proof_check = c; }
	inline void	unsetProofCheck					 		( ) { config.proof_check = 0; }

	// NOTE At most one between reduction time, ratio and number of traversals can be enabled (that is, > 0)
	// Reduction time in seconds
	inline void	setReductionTime						( double time )  { assert(time >= 0); config.proof_red_time = time;}
	// Reduction time as ratio w.r.t. solving time
	inline void	setRatioReductionSolvingTime     		( double ratio ) { assert(ratio >= 0); config.proof_ratio_red_solv = ratio; }
	// Explicit number of graph traversals for each global loop
	inline void	setNumGraphTraversals		     		( int num )	  	 { assert(num >=0 ); config.proof_num_graph_traversals = num; }
	// Number of global reduction loop: each consists of one run of RecyclePivots
	// followed by an amount of graph traversals
	inline void	setNumReductionLoops			 		( int num )      { assert(num >=0 ); config.proof_red_trans = num; }

#endif

	inline void  PrintModel           ( ostream & os ) { solver.printModel( os ); egraph.printModel( os ); }
	void          PrintConfig          ( ostream & os ) { config.printConfig(os); }
	//
	// Misc
	//
	void          PrintResult          ( const lbool &, const lbool & = l_Undef );
	void          DumpAssertionsToFile ( const char * file ) { egraph.dumpAssertionsToFile( file ); }
	void          DumpToFileFunFrog ( const char * file ) { egraph.dumpToFileFunFrog( file ); }
	// Adds a branch heuristic binding to the set of enodes given as argument
	void          addBitBlastBinding   ( vector<Enode*>& v ) { solver.addBB_vector(v); }

	//
	// Add commands to a queue and execute them (used in the parsers)
	//
	int           executeCommands      ( );
	void          addAssert            ( Enode * );               // Command for (assert ...)
	void          addCheckSAT          ( );                       // Command for (check-sat)
	void          addPush              ( int );                   // Command for (push ...)
	void          addPop               ( int );                   // Command for (pop ...)
	void          addGetProof          ( );                       // Command for (get-proof)
	void          addGetInterpolants   ( );                       // Command for (get-interpolants)
	void          addExit              ( );                        // Command for (exit)

	//======================================================================
	//
	// Term Creation API
	//
	//
	// Core functions
	//
	inline Enode * mkTrue      ( )                 { return egraph.mkTrue( ); }
	inline Enode * mkFalse     ( )                 { return egraph.mkFalse( ); }
	inline Enode * mkAnd       ( Enode * e )       { assert( e ); return egraph.mkAnd     ( e ); }
	inline Enode * mkOr        ( Enode * e )       { assert( e ); return egraph.mkOr      ( e ); }
	inline Enode * mkNot       ( Enode * e )       { assert( e ); return egraph.mkNot     ( e ); }
	inline Enode * mkImplies   ( Enode * e )       { assert( e ); return egraph.mkImplies ( e ); }
	inline Enode * mkXor       ( Enode * e )       { assert( e ); return egraph.mkXor     ( e ); }

	inline Enode * mkCons   ( Enode * car, Enode * cdr = NULL )
	{
		assert( car );
		return cdr == NULL ? egraph.cons( car ) : egraph.cons( car, cdr );
	}
	inline Enode * mkCons   ( list< Enode * > & l ) { return egraph.cons( l ); }
	inline Snode * mkCons   ( Snode * car, Snode * cdr = NULL )
	{
		assert( car );
		return cdr == NULL ? sstore.cons( car ) : sstore.cons( car, cdr );
	}
	inline Snode * mkCons   ( list< Snode * > & l )            { return sstore.cons( l ); }

	inline void   mkBind   ( const char * v, Enode * t )      { assert( v ); assert( t ); egraph.mkDefine( v, t ); }
	inline Enode * mkVar    ( const char * n, bool m = false ) { assert( n ); return egraph.mkVar( n, m ); }
	inline Enode * mkFun    ( const char * n, Enode * a )      { assert( n ); return egraph.mkFun( n, a ); }

	//======================================================================
	//
	// Sort Creation API
	//

	inline Snode * mkSortBool  ( )           { return sstore.mkBool  ( ); }
	inline Snode * mkSort      ( Snode * a )      { periplo_error("Arbitrary sort not supported"); }
	inline Snode * mkSortVar   ( const char * n ) { return sstore.mkVar( n ); }

	//======================================================================
	//
	// Getty functions
	//
	inline SATConfig & getConfig    ( )           { return config; }
	inline unsigned    getLearnts   ( )           { return solver.nLearnts( ); }
	inline unsigned    getDecisions ( )           { return solver.decisions; }
	inline lbool       getModel     ( Enode * a ) { return solver.getModel( a ); }

private:

	SATConfig *        config_p;                                   // Pointer to config
	SATConfig &        config;                                     // Reference to config
	SStore *           sstore_p;                                   // Pointer to SStore
	SStore &           sstore;                                     // Reference to SStore
	Egraph *           egraph_p;                                   // Pointer to egraph
	Egraph &           egraph;                                     // Reference to egraph
	SimpSATSolver *    solver_p;                                   // Pointer to solver
	SimpSATSolver &    solver;                                     // Reference to solver
	Tseitin *          cnfizer_p;                                  // Pointer to cnfizer
	Tseitin &          cnfizer;                                    // Reference to cnfizer

	typedef enum
	{
		CMD_UNDEF                                                  // undefined command
		, SET_LOGIC                                                  // (set-logic)
		, SET_OPTION                                                 // (set-option)
		, SET_INFO                                                   // (set-info)
		, DECLARE_SORT                                               // (declare-sort)
		, DEFINE_SORT                                                // (define-sort)
		, DECLARE_FUN                                                // (declare-fun)
		, DEFINE_FUN                                                 // (define-fun)
		, PUSH                                                       // (push)
		, POP                                                        // (pop)
		, ASSERT                                                     // (assert)
		, CHECK_SAT                                                  // (check-sat)
		, GET_ASSERTIONS                                             // (get-assertions)
		, GET_PROOF                                                  // (get-proof)
		, GET_INTERPOLANTS                                           // (get-interpolants)
		, GET_UNSAT_CORE                                             // (get-unsat-core)
		, GET_VALUE                                                  // (get-value)
		, GET_ASSIGNMENT                                             // (get-assignment)
		, GET_OPTION                                                 // (get-option)
		, GET_INFO                                                   // (get-info)
		, EXIT                                                       // (exit)
	} command_name_t;

	struct Command
	{
		Command( )
		: command( CMD_UNDEF )
		, enode    ( NULL )
		, sort_arg ( NULL )
		, sort_ret ( NULL )
		{ }

		command_name_t command;
		Enode *        enode;
		Snode *        sort_arg;
		Snode *        sort_ret;
		char           str[256];
		int            num;
	};

	//int     executeIncremental   ( );                                // Execute with incremental ability
	int     executeStatic        ( );                                 // Execute without incremental ability (faster as more preproc is done)
	lbool   CheckSAT              ( );                            		// Command for (check-sat)
	lbool   CheckSAT              ( vec< Enode * > & );                      // Command for (check-sat)
	lbool   CheckSAT              ( vec< Enode * > &, unsigned );            // Command for (check-sat)
	void    GetProof             ( );
	void    GetInterpolants      ( );
	void    staticCheckSATNointerp       ( );                                 // For when only one check is required
#ifdef PRODUCE_PROOF
	void    staticCheckSATInterp ( );                                // For when only one check is required
#endif

	lbool              state;                                      // Current state of the solver
	vector< Command >  command_list;                               // Store commands to execute
	unsigned          nof_checksat;                               // Counter for CheckSAT commands
	unsigned           counter;                                    // Counter for creating new terms
	bool               init;                                       // Initialize
	bool               model_computed;
	unsigned		   next_partition;							    // Index of next partition asserted
};
}

#endif
