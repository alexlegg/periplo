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

#ifndef EGRAPH_H
#define EGRAPH_H


#include "Enode.h"
#include "SStore.h"
#include "SigTab.h"
#include "SplayTree.h"
#include "SATConfig.h"
#include "SolverTypes.h"
//#include <ext/hash_set>
#include <tr1/unordered_set>

namespace periplo {
class SimpSATSolver;
}

namespace periplo {

class Egraph
{
public:

	Egraph( SATConfig & c, SStore & s )
	: enil               ( new Enode )
	, id     ( 0 )
	, config ( c )
	, solver             ( NULL )
	, sort_store         ( s )
	, active_dup1        ( false )
	, active_dup2        ( false )
	, dup_count1         ( 0 )
	, dup_count2         ( 0 )
	, active_dup_map1    ( false )
	, active_dup_map2    ( false )
	, dup_map_count1     ( 0 )
	, dup_map_count2     ( 0 )
	, theoryInitialized  ( false )
	, time_stamp         ( 0 )
	, use_gmp		   ( false )
#ifdef PRODUCE_PROOF
	, iformula           ( 1 )
#endif
	{
		//
		// Initialize nil key for splay tree
		//
		Enode * nilKey = const_cast< Enode * >( enil );
		store.setNil( nilKey );
		id_to_enode.push_back( const_cast< Enode * >( enil ) );
	}

	~Egraph( )
	{
		backtrackToStackSize( 0 );

		//
		// Delete enodes
		//
		while ( !id_to_enode.empty( ) )
		{
			if ( id_to_enode.back( ) != NULL )
				delete id_to_enode.back( );
			id_to_enode.pop_back( );
		}
	}

	size_t size() const { return id_to_enode.size(); };

	//
	// Predefined constants nil, true, false
	//
	const Enode * const enil;
	Enode * etrue;
	Enode * efalse;

	//===========================================================================
	// Public APIs for enode construction/destruction

	Enode *  newSymbol           ( const char *, Snode *, Snode *, uint64_t = 0 );                 // Creates a new symbol
	Enode *  cons                ( list< Enode * > & );                                            // Shortcut, but not efficient
	Enode *  cons                ( Enode **, unsigned );                                           // Shortcut
	Enode *  cons                ( Enode *, Enode * );                                             // Create Lists/Terms
	Enode *  cons                ( Enode *, Enode *, bool & );                                     // Create Lists/Terms; notifies if already existent
	Enode *  cons                ( Enode * e ) { return cons( e, const_cast< Enode * >(enil) ); }  // Shortcut for singleton
	//
	// Specialized functions
	//
	inline Enode * mkTrue        ( )              { return etrue; }
	inline Enode * mkFalse       ( )              { return efalse; }
	//
	// Implemented in EgraphStore.C
	// Semantic of mk* functions: they use
	// the concrete cons, and they store the
	// node permanently inside the term bank
	//
	Enode * mkNot              ( Enode * );
	Enode * mkAnd              ( Enode * );
	Enode * mkIff              ( Enode * );
	Enode * mkOr               ( Enode * );
	Enode * mkImplies          ( Enode * );
	Enode * mkXor              ( Enode * );

	Enode * allocTrue          ( );
	Enode * allocFalse         ( );

	Enode * mkVar              ( const char *, bool = false );
	Enode * mkFun              ( const char *, Enode * );

	void    mkDefine           ( const char *, Enode * );
	Enode * getDefine          ( const char * );

	Enode * getUncheckedAssertions  ( );

	void    printEnodeList          ( ostream & );
	void    addAssertion            ( Enode * );

	void          initializeStore   ( );
	inline void   addSubstitution   ( Enode * s, Enode * t ) { top_level_substs.push_back( make_pair( s, t ) ); }
	inline void   setTopEnode       ( Enode * e )            { assert( e ); top = e; }
	inline size_t nofEnodes         ( )                      { return id_to_enode.size( ); }
	inline Enode*	getEnode( enodeid_t id ) { assert( id < id_to_enode.size() ); return id_to_enode[id]; }

	Enode * copyEnodeEtypeTermWithCache   ( Enode *, bool = false );
	Enode * copyEnodeEtypeListWithCache   ( Enode *, bool = false );
	Enode * maximize                      ( Enode * );

	void        printMemStats             ( ostream & );
	//
	// Fast duplicates checking. Cannot be nested !
	//
	inline void initDup1  ( )           { assert( !active_dup1 ); active_dup1 = true; duplicates1.resize( id_to_enode.size( ), dup_count1 ); dup_count1 ++; }
	inline void storeDup1 ( Enode * e ) { assert(  active_dup1 ); assert( e->getId( ) < (enodeid_t)duplicates1.size( ) ); duplicates1[ e->getId( ) ] = dup_count1; }
	inline bool isDup1    ( Enode * e ) { assert(  active_dup1 ); assert( e->getId( ) < (enodeid_t)duplicates1.size( ) ); return duplicates1[ e->getId( ) ] == dup_count1; }
	inline void doneDup1  ( )           { assert(  active_dup1 ); active_dup1 = false; }
	//
	// Fast duplicates checking. Cannot be nested !
	//
	inline void initDup2  ( )           { assert( !active_dup2 ); active_dup2 = true; duplicates2.resize( id_to_enode.size( ), dup_count2 ); dup_count2 ++; }
	inline void storeDup2 ( Enode * e ) { assert(  active_dup2 ); assert( e->getId( ) < (enodeid_t)duplicates2.size( ) ); duplicates2[ e->getId( ) ] = dup_count2; }
	inline bool isDup2    ( Enode * e ) { assert(  active_dup2 ); assert( e->getId( ) < (enodeid_t)duplicates2.size( ) ); return duplicates2[ e->getId( ) ] == dup_count2; }
	inline void doneDup2  ( )           { assert(  active_dup2 ); active_dup2 = false; }
	//
	// Fast duplicates checking. Cannot be nested !
	//
	void    initDupMap1  ( );
	void    storeDupMap1 ( Enode *, Enode * );
	Enode * valDupMap1   ( Enode * );
	void    doneDupMap1  ( );

	void    initDupMap2  ( );
	void    storeDupMap2 ( Enode *, Enode * );
	Enode * valDupMap2   ( Enode * );
	void    doneDupMap2  ( );

	void    computePolarities ( Enode * );

	void dumpAssertionsToFile ( const char * );
	void dumpHeaderToFile     ( ostream &, logic_t = UNDEF );
	void dumpFormulaToFile    ( ostream &, Enode *, bool = false );
	void dumpToFile           ( const char *, Enode * );
    void dumpToFileFunFrog    ( const char *);

	//===========================================================================
	// Public APIs for Egraph Core Solver

public:
	void		      	initializeSolver ( SimpSATSolver * );          // Attaches ordinary solver
	periplo::minisat::lbool inform                  ( Enode * );                  // Inform the solver about the existence of a theory atom
	void                pushBacktrackPoint      ( );                          // Push a backtrack point
	void                popBacktrackPoint       ( );                          // Backtrack to last saved point
	void                computeModel            ( );
	void                printModel              ( ostream &	);                // Computes and print the model
	inline void         setUseGmp               ( ) { use_gmp = true; }
	inline bool         getUseGmp               ( ) { return use_gmp; }
	bool                checkDupClause          ( Enode *, Enode * );         // Check if a clause is duplicate
	void                explain                 ( Enode *, Enode *, vector< Enode * > & );      // Exported explain
	//===========================================================================
	// Exported function for using egraph as supporting solver

	bool                extAssertLit            ( Enode * );                  // Assert a theory literal
	void                extPushBacktrackPoint   ( );                          // Push a backtrack point
	void                extPopBacktrackPoint    ( );                          // Backtrack to last saved point

private:

	// CoreTSolver data
	const int                   id;               // Id of the solver
	SATConfig &                 config;           // Reference to configuration
	vector< size_t >            backtrack_points; // Keeps track of backtrack points
	SimpSATSolver *             solver;              // Pointer to solver
	inline void                 setSolver      ( SimpSATSolver * s ) { assert( s ); assert( solver == NULL ); solver = s; }


	//===========================================================================
	// Private Routines for enode construction/destruction

	SStore & sort_store;
	Snode * sarith1;
	Snode * sarray;
	Snode * sindex;
	Snode * selem;

	//
	// Defines the set of operations that can be performed and that should be undone
	//
	// FIXME Why is SYMB never added to undo_stack_oper ??
	// FIXME INSERT_STORE does not work either -> see EgraphStore.C, line 408
	typedef enum {      // These constants are stored on undo_stack_oper when
		SYMB            // A new symbol is created
		, INSERT_STORE    // Inserted in store
	} oper_t;
	//
	// Handy function to swap two arguments of a list
	//
	inline Enode * swapList ( Enode * args )
	{
		assert( args );
		assert( args->isList( ) );
		assert( args->getArity( ) == 2 );
		return cons( args->getCdr( )->getCar( ), cons( args->getCar( ) ) );
	}
	//
	// Related to term creation
	//
	void    insertSymbol ( Enode * );                             // Inserts a symbol
	void    removeSymbol ( Enode * );                             // Remove a symbol
	Enode * lookupSymbol ( const char * name );                   // Retrieve a symbol
	void    insertDefine ( const char *, Enode * );               // Insert a define
	Enode * lookupDefine ( const char * );                        // Retrieve a define
	Enode * insertStore  ( const enodeid_t, Enode *, Enode * );   // Insert node into the global store
	void    removeStore  ( Enode * );                             // Remove a node from the global store
	//
	// Related to congruence closure
	//
	Enode * insertSigTab ( const enodeid_t, Enode *, Enode * );   // For undoable cons only
	Enode * insertSigTab ( Enode * );                             // For for terms that go in the congruence
	Enode * lookupSigTab ( Enode * );                             // Retrieve Enode
	void    removeSigTab ( Enode * );                             // Remove Enode from sig_tab

	bool                        active_dup1;                      // To prevent nested usage
	bool                        active_dup2;                      // To prevent nested usage
	vector< int >               duplicates1;                      // Fast duplicate checking
	vector< int >               duplicates2;                      // Fast duplicate checking
	int                         dup_count1;                       // Current dup token
	int                         dup_count2;                       // Current dup token
	bool                        active_dup_map1;                  // To prevent nested usage
	bool                        active_dup_map2;                  // To prevent nested usage
	vector< Enode * >           dup_map1;                         // Fast duplicate checking
	vector< int >               dup_set1;                         // Fast duplicate checking
	vector< Enode * >           dup_map2;                         // Fast duplicate checking
	vector< int >               dup_set2;                         // Fast duplicate checking
	int                         dup_map_count1;                   // Current dup token
	int                         dup_map_count2;                   // Current dup token
	map< string, Enode * >      name_to_symbol;                   // Store for symbols
	map< string, Enode * >      name_to_define;                   // Store for defines

	SplayTree< Enode *, Enode::idLessThan > store;                // The actual store
	SigTab                                  sig_tab;		// (Supposely) Efficient Signature table for congruence closure

	vector< Enode * >              id_to_enode;                   // Table ENODE_ID --> ENODE
	vector< int >                  id_to_belong_mask;             // Table ENODE_ID --> ENODE
	vector< int >                  id_to_fan_in;                  // Table ENODE_ID --> fan in
	list< Enode * >                assertions;                    // List of assertions
	vector< Enode * >              cache;                         // Cache simplifications
	Enode *                        top;                           // Top node of the formula
	map< Pair( int ), Enode * >    ext_store;                     // For fast extraction handling
	vector< Enode * >              se_store;                      // For fast sign extension
	vector< int >                  id_to_inc_edges;               // Keeps track of how many edges enter an enode
	set< Enode * >                 variables;                     // List of variables
	vector< Pair( Enode * ) >      top_level_substs;              // Keep track of substitutions in TopLevelProp.C
	bool                           model_computed;                // Has model been computed lately ?

	//===========================================================================
	//
	// Backtracking
	//
	void backtrackToStackSize ( size_t );                         // Backtrack to a certain operation

	inline const char * logicStr ( logic_t l )
	{
		if ( l == EMPTY )     return "EMPTY";
		else if ( l == QF_UF )     return "QF_UF";
		else if ( l == QF_BV )     return "QF_BV";
		else if ( l == QF_RDL )    return "QF_RDL";
		else if ( l == QF_IDL )    return "QF_IDL";
		else if ( l == QF_LRA )    return "QF_LRA";
		else if ( l == QF_LIA )    return "QF_LIA";
		else if ( l == QF_UFRDL )  return "QF_UFRDL";
		else if ( l == QF_UFIDL )  return "QF_UFIDL";
		else if ( l == QF_UFLRA )  return "QF_UFLRA";
		else if ( l == QF_UFLIA )  return "QF_UFLIA";
		else if ( l == QF_UFBV )   return "QF_UFBV";
		else if ( l == QF_AX )     return "QF_AX";
		else if ( l == QF_AXDIFF ) return "QF_AXDIFF";
		else if ( l == QF_BOOL )   return "QF_BOOL";
		return "";
	}

	bool                        theoryInitialized;                // True if theory solvers are initialized
	bool                        state;                            // the hell is this ?
	set< enodeid_t >            initialized;                      // Keep track of initialized nodes
	map< enodeid_t, periplo::minisat::lbool >     informed;                         // Keep track of informed nodes
	vector< Enode * >           undo_stack_term;                  // Keeps track of terms involved in operations
	vector< oper_t >            undo_stack_oper;                  // Keeps track of operations

	int                         time_stamp;                       // Need for finding NCA
	bool                        use_gmp;                          // Do we have to use gmp?

	//============================================================================

#ifdef BUILD_64
	std::tr1::unordered_set< enodeid_pair_t >     clauses_sent;
	//__gnu_cxx::hash_set< enodeid_pair_t >     clauses_sent;
#else
	std::tr1::unordered_set< Pair( enodeid_t ) > clauses_sent;
	//__gnu_cxx::hash_set< Pair( enodeid_t ) >  clauses_sent;
#endif

#ifdef PRODUCE_PROOF
	//===========================================================================
	// Interpolation related routines - Implemented in EgraphDebug.C

public:
	inline unsigned getNofPartitions        ( ) { return iformula - 1; }

	Enode *         getNextAssertion        ( );
	Enode *         expandDefinitions       ( Enode * );
	void            addDefinition           ( Enode *, Enode * );
	void            maximizeColors          ( );
private:

	inline void     formulaToTag     ( Enode * e ) { formulae_to_tag.push_back( e ); }

	void            addIFormula      ( );
	void            tagIFormulae     ( const ipartitions_t & );
	void            tagIFormulae     ( const ipartitions_t &, vector< Enode * > & );
	void            tagIFormula      ( Enode *, const ipartitions_t & );

	void            scanForDefs      ( Enode *, set< Enode * > & );
	Enode *         substitute       ( Enode *, map< Enode *, Enode * > & );

	unsigned                iformula;                  // Current formula id
	vector< Enode * >       formulae_to_tag;           // Formulae to be tagged
	vector< uint64_t >      id_to_iformula;            // From enode to iformula it belongs to
	vector< Enode * >       idef_list;                 // Definition list in rev chron order
	map< Enode *, Enode * > idef_map;                  // Def to term map
#endif                                                                      

	void printStatistics ( ofstream & );
};
}

inline void periplo::Egraph::initDupMap1( )
{ 
	assert( !active_dup_map1 );
	active_dup_map1 = true;
	dup_map1.resize( id_to_enode.size( ), NULL );
	dup_set1.resize( id_to_enode.size( ), dup_map_count1 );
	dup_map_count1 ++;
}

inline void periplo::Egraph::initDupMap2( )
{ 
	assert( !active_dup_map2 );
	active_dup_map2 = true;
	dup_map2.resize( id_to_enode.size( ), NULL );
	dup_set2.resize( id_to_enode.size( ), dup_map_count2 );
	dup_map_count2 ++;
}

inline void periplo::Egraph::storeDupMap1( Enode * k, Enode * e ) 
{ 
	assert(  active_dup_map1 );
	dup_map1.resize( id_to_enode.size( ), NULL );
	dup_set1.resize( id_to_enode.size( ), dup_map_count1 - 1 );
	assert( k->getId( ) < (enodeid_t)dup_set1.size( ) );
	dup_set1[ k->getId( ) ] = dup_map_count1;
	dup_map1[ k->getId( ) ] = e;
}

inline void periplo::Egraph::storeDupMap2( Enode * k, Enode * e ) 
{ 
	assert(  active_dup_map2 );
	dup_map2.resize( id_to_enode.size( ), NULL );
	dup_set2.resize( id_to_enode.size( ), dup_map_count2 - 1 );
	assert( k->getId( ) < (enodeid_t)dup_set2.size( ) );
	dup_set2[ k->getId( ) ] = dup_map_count2;
	dup_map2[ k->getId( ) ] = e;
}

inline periplo::Enode * periplo::Egraph::valDupMap1( Enode * k )
{ 
	assert(  active_dup_map1 );
	dup_map1.resize( id_to_enode.size( ), NULL );
	dup_set1.resize( id_to_enode.size( ), dup_map_count1 - 1 );
	assert( k->getId( ) < (enodeid_t)dup_set1.size( ) );
	if ( dup_set1[ k->getId( ) ] == dup_map_count1 )
		return dup_map1[ k->getId( ) ];
	return NULL;
}

inline periplo::Enode * periplo::Egraph::valDupMap2( Enode * k )
{ 
	assert(  active_dup_map2 );
	dup_map2.resize( id_to_enode.size( ), NULL );
	dup_set2.resize( id_to_enode.size( ), dup_map_count2 - 1 );
	assert( k->getId( ) < (enodeid_t)dup_set2.size( ) );
	if ( dup_set2[ k->getId( ) ] == dup_map_count2 )
		return dup_map2[ k->getId( ) ];
	return NULL;
}

inline void periplo::Egraph::doneDupMap1( ) 
{ 
	assert(  active_dup_map1 );
	active_dup_map1 = false;
}

inline void periplo::Egraph::doneDupMap2( ) 
{ 
	assert(  active_dup_map2 );
	active_dup_map2 = false;
}

#endif
