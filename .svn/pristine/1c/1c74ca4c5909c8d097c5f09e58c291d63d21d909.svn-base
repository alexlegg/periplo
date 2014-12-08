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

/****************************************************************************************[Solver.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#ifndef MINISAT_SOLVER_H
#define MINISAT_SOLVER_H

#include <cstdio>
#include "Vec.h"
#include "Heap.h"
#include "Alg.h"
#include "Options.h"
#include "SolverTypes.h"

#include "EnodeHandler.h"
#include "Global.h"
#include "Egraph.h"
#include "SATConfig.h"

#ifdef PRODUCE_PROOF
#include "PG.h"
#include "Proof.h"
namespace periplo { 
class Proof;
class ProofGraph;
}
#endif

using periplo::minisat::Var;
using periplo::minisat::Lit;
using periplo::minisat::Clause;
using periplo::minisat::vec;
using periplo::minisat::lbool;
using periplo::minisat::CRef;
using periplo::minisat::ClauseAllocator;
using periplo::minisat::OccLists;
using periplo::minisat::Heap;
using periplo::minisat::Map;
using periplo::minisat::CRef_Undef;
using periplo::minisat::lit_Undef;

namespace periplo {

//=================================================================================================
// Added Code
struct VarHash { uint32_t operator () (Var v) const { return v; } };
//template<>
//struct Equal<Var> { bool operator () (Var v1, Var v2) const { return v1 == v2; };
// Added Code
//=================================================================================================

//=================================================================================================
// Solver -- the main class:

class CoreSATSolver
{
public:
	// Constructor/Destructor:
	//
	CoreSATSolver( Egraph &, SATConfig & );
	virtual ~CoreSATSolver();

	//=================================================================================================
	// Added Code
	void     initialize       ( );
#ifdef PRODUCE_PROOF
	void 	 clearDataStructures ( );
#endif
	// Added Code
	//=================================================================================================

	// Problem specification:
	//
	Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

#ifdef PRODUCE_PROOF
	bool    addClause (const vec<Lit>& ps, const ipartitions_t& = 0);		// Add a clause to the solver.
	bool    addEmptyClause(const ipartitions_t& = 0);                       // Add the empty clause, making the solver contradictory.
	bool    addClause (Lit p, const ipartitions_t& = 0);            		// Add a unit clause to the solver.
	bool    addClause (Lit p, Lit q, const ipartitions_t& = 0);    			// Add a binary clause to the solver.
	bool    addClause (Lit p, Lit q, Lit r, const ipartitions_t& = 0);    	// Add a ternary clause to the solver.
	bool    addClause_( vec<Lit>& ps, const ipartitions_t& = 0); 			// Add a clause to the solver without making superflous internal copy. Will
#else
	bool    addClause (const vec<Lit>& ps);						// Add a clause to the solver.
	bool    addEmptyClause();                                     // Add the empty clause, making the solver contradictory.
	bool    addClause (Lit p);            							// Add a unit clause to the solver.
	bool    addClause (Lit p, Lit q );   							// Add a binary clause to the solver.
	bool    addClause (Lit p, Lit q, Lit r  );  				 	// Add a ternary clause to the solver.
	bool    addClause_( vec<Lit>& ps );  							// Add a clause to the solver without making superflous internal copy. Will
#endif
	// change the passed vector 'ps'.

	// Solving:
	//
	bool    simplify     ();                        // Removes already satisfied clauses.
	bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
	lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
	bool    solve        ();                        // Search without assumptions.
	bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
	bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
	bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
	bool    okay         () const;                  // FALSE means solver is in a conflicting state

	void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
	void    toDimacs     (const char *file, const vec<Lit>& assumps);
	void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

	// Convenience versions of 'toDimacs()':
	void    toDimacs     (const char* file);
	void    toDimacs     (const char* file, Lit p);
	void    toDimacs     (const char* file, Lit p, Lit q);
	void    toDimacs     (const char* file, Lit p, Lit q, Lit r);

	// Variable mode:
	//
	void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
	void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

	// Read state:
	//
	lbool   value      (Var x) const;       // The current value of a variable.
	lbool   value      (Lit p) const;       // The current value of a literal.
	lbool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
	lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
	int     nAssigns   ()      const;       // The current number of assigned literals.
	int     nClauses   ()      const;       // The current number of original clauses.
	int     nLearnts   ()      const;       // The current number of learnt clauses.
	int     nVars      ()      const;       // The current number of variables.
	int     nFreeVars  ()      const;

	// Resource contraints:
	//
	void    setConfBudget(int64_t x);
	void    setPropBudget(int64_t x);
	void    budgetOff();
	void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
	void    clearInterrupt();     // Clear interrupt indicator flag.

	// Memory management:
	//
	virtual void garbageCollect();
	void    checkGarbage(double gf);
	void    checkGarbage();

	//=================================================================================================
	// Added Code
	void addNewAtom         ( Enode * );

	// External support incremental and backtrackable APIs
	void        pushBacktrackPoint ( );
	void        popBacktrackPoint  ( );
	void        reset              ( );
	inline void restoreOK          ( )       { ok = true; }
	inline bool isOK               ( ) const { return ok; }

	// TODO restore
	//void     verifyModel      ();

	void     printClause   ( ostream &, CRef );
	void 	  printClause	 ( ostream &, Clause& );
	void     printClause   ( ostream &, vec< Lit > &, bool = false );
	void     printClause   ( ostream &, vector< Lit > &, bool = false );

	bool    use_bb_heur;        // Use the bit blasting heuristic to branch on bit blasted literal
	double learnts_size;
	uint64_t all_learnts;

	// Added Code
	//=================================================================================================

	// Extra results: (read-only member variable)
	//
	vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
	vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
	// this vector represent the final conflict clause expressed in the assumptions.

	// Mode of operation:
	//
	int       verbosity;
	double    var_decay;
	double    clause_decay;
	double    random_var_freq;
	double    random_seed;
	bool      luby_restart;
	int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
	int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
	bool      rnd_pol;            // Use random polarities for branching heuristics.
	bool      rnd_init_act;       // Initialize variable activities with a small random value.
	double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.

	int       restart_first;      // The initial restart limit.                                                                (default 100)
	double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
	double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
	double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

	int       learntsize_adjust_start_confl;
	double    learntsize_adjust_inc;

	// Statistics: (read-only member variable)
	//
	uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
	uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;

	//=================================================================================================
	// Added Code
	// NOTE added to allow verification of partial interpolants in ProofInterpolator.C
#ifdef PRODUCE_PROOF
	vec<CRef>&  getClauses() { return clauses; }
	vector< pair< CRef, ipartitions_t > >& getUnits() { return units_to_partition; }
#endif
	// Added Code
	//=================================================================================================

protected:
	//=================================================================================================
	// Added Code
	EnodeHandler *  enode_handler; // Handles enodes
	Egraph &    egraph;         // Stores sgraph
	SATConfig & config;         // Stores Config
	// Added Code
	//=================================================================================================


	// Helper structures:
	//
	struct VarData { CRef reason; int level; };
	static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

	struct Watcher {
		CRef cref;
		Lit  blocker;
		Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
		//=================================================================================================
		// Added Code
		Watcher() : cref(CRef_Undef), blocker(lit_Undef) {}
		// Added Code
		//=================================================================================================
		bool operator==(const Watcher& w) const { return cref == w.cref; }
		bool operator!=(const Watcher& w) const { return cref != w.cref; }
	};

	//=================================================================================================
	// Added Code
	struct watcher_lt
	{
		const ClauseAllocator& ca;
		watcher_lt(const ClauseAllocator& ca_) : ca(ca_) {}
		bool operator () (const Watcher& x, const Watcher& y) {
			return ca[x.cref].size() < ca[y.cref].size(); }
	};
	// Added Code
	//=================================================================================================

	struct WatcherDeleted
	{
		const ClauseAllocator& ca;
		WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
		bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
	};

	struct VarOrderLt {
		const vec<double>&  activity;
		bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
		VarOrderLt(const vec<double>&  act) : activity(act) { }
	};

	// Solver state:
	//
	bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
	vec<CRef>           clauses;          // List of problem clauses.
	vec<CRef>           learnts;          // List of learnt clauses.
	double              cla_inc;          // Amount to bump next clause with.
	vec<double>         activity;         // A heuristic measurement of the activity of a variable.
	double              var_inc;          // Amount to bump next variable with.
	OccLists<Lit, vec<Watcher>, WatcherDeleted>
	watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
	vec<lbool>          assigns;          // The current assignments.
	vec<char>           polarity;         // The preferred polarity of each variable.
	vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
	vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
	vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
	//=================================================================================================
	// Added Code
#ifdef PRODUCE_PROOF
	// FIXME trail_pos is useless at the moment
	vec<int>            trail_pos;        // 'trail_pos[var]' is the variable's position in 'trail[]'. This supersedes 'level[]' in some sense, and 'level[]' will probably be removed in future releases.
	vec<Lit>            analyze_proof;
	vec< CRef >    	     units;
#endif
	// Added Code
	//=================================================================================================
	vec<VarData>        vardata;          // Stores reason and level for each variable.
	int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
	int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
	int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
	vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
	Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
	double              progress_estimate;// Set by 'search()'.
	bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

	ClauseAllocator     ca;

	// Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
	// used, exept 'seen' wich is used in several places.
	//
	vec<char>           seen;
	vec<Lit>            analyze_stack;
	vec<Lit>            analyze_toclear;
	vec<Lit>            add_tmp;

	double              max_learnts;
	double              learntsize_adjust_confl;
	int                 learntsize_adjust_cnt;

	// Resource contraints:
	//
	int64_t             conflict_budget;    // -1 means no budget.
	int64_t             propagation_budget; // -1 means no budget.
	bool                asynch_interrupt;

	// Main internal methods:
	//
	void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
	Lit      pickBranchLit    ();                                                      // Return the next decision variable.
	void     newDecisionLevel ();                                                      // Begins a new decision level.
	void     uncheckedEnqueue (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
	bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
	CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
	void     cancelUntil      (int level);                                             // Backtrack until a certain level.
	void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel);    // (bt = backtrack)
	void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
	bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
	lbool    search           (int nof_conflicts);                                     // Search for a given number of conflicts.
	lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
	void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
	void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
	void     rebuildOrderHeap ();

	// Maintaining Variable/Clause activity:
	//
	void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
	void     varBumpActivity  (Var v, double inc);     // Increase a variable with the current 'bump' value.
	void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
	void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
	void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

	// Operations on clauses:
	//
	void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
	void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
	void     removeClause     (CRef cr);               // Detach and free a clause.
	bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
	bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

	void     relocAll         (ClauseAllocator& to);

	// Misc:
	//
	int      decisionLevel    ()      const; // Gives the current decisionlevel.
	uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
	CRef     reason           (Var x) const;
	//=================================================================================================
	// Added Code
	void     setReason( Var x, CRef c );
	// Added Code
	//=================================================================================================
	int      level            (Var x) const;
	double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
	bool     withinBudget     ()      const;

	// Static helpers:
	//

	// Returns a random float 0 <= x < 1. Seed must never be 0.
	static inline double drand(double& seed) {
		seed *= 1389796;
		int q = (int)(seed / 2147483647);
		seed -= (double)q * 2147483647;
		return seed / 2147483647; }

	// Returns a random integer 0 <= x < size. Seed must never be 0.
	static inline int irand(double& seed, int size) {
		return (int)(drand(seed) * size); }

	//=================================================================================================
	// Added Code

public:
	void     printLit         ( Lit l );
	void     printClause      ( CRef );
	void 	  printClause		( Clause& );
	void     printClause      ( vec< Lit > & );
	lbool 	  satSolve                ( );             // Solve
	lbool  getModel               ( Enode * );
	void   printModel             ( );             // Wrapper
	void   printModel             ( ostream & );   // Prints model
#ifdef PRODUCE_PROOF
	void   printProofSMT2              ( ostream & );   // Print proof
	void   printProofDotty              ( );   // Print proof
	void   printInter              ( ostream & );   // Generate and print interpolants
	void   getInterpolants         (const vector<vector<int> >& partitions, vector<Enode*>& interpolants);
	void   setColoringSuggestions	(  vector< std::map<Enode*, icolor_t>* > * mp );
	bool   getPathInterpolants(vector<Enode*>& interpolants);
	void   getSingleInterpolant(vector<Enode*>& interpolants);
	bool   getSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants);
	bool   getGenSimultaneousAbstractionInterpolants(vector<Enode*>& interpolants);
	bool   getStateTransitionInterpolants(vector<Enode*>& interpolants);
	bool   getTreeInterpolants(InterpolationTree*, vector<Enode*>& interpolants);
	bool   checkImplication( Enode* f1, Enode* f2);

	void   createProofGraph		 ();
	inline ProofGraph* getProofGraph()			 { return proof_graph; }
	void   deleteProofGraph		 ();
	void   reduceProofGraph		 ();
	void   checkPartitions       ();
	inline ipartitions_t & getIPartitions ( CRef c )            { assert( clause_to_partition.find( c ) != clause_to_partition.end( ) ); return clause_to_partition[ c ]; }
#endif

protected:

	void   printStatistics        ( ostream & );   // Prints statistics
	void   printTrail             ( );             // Prints the trail (debugging)

	// Backtrackability
	void   cancelUntilVar         ( Var );         // Backtrack until a certain variable
	void   cancelUntilVarTempInit ( Var );         // Backtrack until a certain variable
	void   cancelUntilVarTempDone ( );             // Backtrack until a certain variable

	int    restartNextLimit       ( int );         // Next conflict limit for restart

	void   dumpCNF                ( );             // Dumps CNF to cnf.smt2
	void   dumpRndInter           ( );             // Dumps a random interpolation problem

	// Added by Grisha
	void   addBB                  ( vec<Var>& );   // Add a bit blasted variable group

	unsigned           luby_i;                     // Keep track of luby index
	unsigned           luby_k;                     // Keep track of luby k
	vector< unsigned > luby_previous;              // Previously computed luby numbers

#ifdef PRODUCE_PROOF
	//
	// Proof production
	//
	Proof *             proof_;                   // (Pointer to) Proof store
	Proof &             proof;                    // Proof store
	ProofGraph *		proof_graph;			  // Proof graph
	vec< CRef >     pleaves;                  // Store clauses that are still involved in the proof
	// TODO: Maybe change to vectors
	vector< pair< CRef, ipartitions_t > > units_to_partition;  // Unit clauses and their partitions
	map< CRef, ipartitions_t >            clause_to_partition; // Clause id to interpolant partition
#endif

	double             preproc_time;
	bool               init;

	//
	// Added by Grisha
	// bit blasting heuristic data
	//
	vec<Var>*                  bb_siblings;
	Map<Var,vec<Var>*,VarHash> bb_vars;
	//
	// Data structures required for incrementality, backtrackability
	//
	vec<Lit>           lit_to_restore;             // For cancelUntilVarTemp
	vec<lbool>          val_to_restore;             // For cancelUntilVarTemp
	set< CRef >    detached;

	enum oper_t
	{
		NEWVAR
		, NEWUNIT
		, NEWCLAUSE
		, NEWLEARNT
#ifdef PRODUCE_PROOF
		, NEWPROOF
#endif
	};
	//
	// Automatic push and pop, for enable undo
	//
	vector< size_t >   undo_stack_size;            // Keep track of stack_oper size
	vector< oper_t >   undo_stack_oper;            // Keep track of operations
	vector< void * >   undo_stack_elem;            // Keep track of aux info
	vector< int >      undo_trail_size;            // Keep track of trail size
	//=================================================================================================
};
}


//=================================================================================================
// Implementation of inline methods:
//=================================================================================================
// Added Code
inline void periplo::CoreSATSolver::setReason( Var x, CRef c ) { vardata[x].reason = c; }
// Added Code
//=================================================================================================
inline CRef periplo::CoreSATSolver::reason(Var x) const { return vardata[x].reason; }
inline int  periplo::CoreSATSolver::level (Var x) const { return vardata[x].level; }

inline void periplo::CoreSATSolver::insertVarOrder(Var x) {
	if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void periplo::CoreSATSolver::varDecayActivity() { var_inc *= (1 / var_decay); }
inline void periplo::CoreSATSolver::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }
inline void periplo::CoreSATSolver::varBumpActivity(Var v, double inc) {
	if ( (activity[v] += inc) > 1e100 ) {
		// Rescale:
		for (int i = 0; i < nVars(); i++)
			activity[i] *= 1e-100;
		var_inc *= 1e-100; }

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v))
		order_heap.decrease(v); }

inline void periplo::CoreSATSolver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void periplo::CoreSATSolver::claBumpActivity (Clause& c) {
	if ( (c.activity() += cla_inc) > 1e20 ) {
		// Rescale:
		for (int i = 0; i < learnts.size(); i++)
			ca[learnts[i]].activity() *= 1e-20;
		cla_inc *= 1e-20; } }


inline void periplo::CoreSATSolver::checkGarbage(void) { return checkGarbage(garbage_frac); }
inline void periplo::CoreSATSolver::checkGarbage(double gf){
#ifndef PRODUCE_PROOF
	// FIXME Relocation not compatible at the moment with proof tracking
	if (ca.wasted() > ca.size() * gf) garbageCollect();
#endif
}

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     periplo::CoreSATSolver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
#ifdef PRODUCE_PROOF
inline bool     periplo::CoreSATSolver::addClause       (const vec<Lit>& ps, const ipartitions_t& in)    { ps.copyTo(add_tmp); return addClause_(add_tmp, in); }
inline bool     periplo::CoreSATSolver::addEmptyClause  ( const ipartitions_t& in)                      { add_tmp.clear(); return addClause_(add_tmp, in); }
inline bool     periplo::CoreSATSolver::addClause       (Lit p, const ipartitions_t& in)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp, in); }
inline bool     periplo::CoreSATSolver::addClause       (Lit p, Lit q, const ipartitions_t& in)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp, in); }
inline bool     periplo::CoreSATSolver::addClause       (Lit p, Lit q, Lit r, const ipartitions_t& in)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp, in); }
#else
inline bool     periplo::CoreSATSolver::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     periplo::CoreSATSolver::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     periplo::CoreSATSolver::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     periplo::CoreSATSolver::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     periplo::CoreSATSolver::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
#endif
inline bool     periplo::CoreSATSolver::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c; }
inline void     periplo::CoreSATSolver::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      periplo::CoreSATSolver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t periplo::CoreSATSolver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    periplo::CoreSATSolver::value         (Var x) const   { return assigns[x]; }
inline lbool    periplo::CoreSATSolver::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    periplo::CoreSATSolver::modelValue    (Var x) const   { return model[x]; }
inline lbool    periplo::CoreSATSolver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      periplo::CoreSATSolver::nAssigns      ()      const   { return trail.size(); }
inline int      periplo::CoreSATSolver::nClauses      ()      const   { return clauses.size(); }
inline int      periplo::CoreSATSolver::nLearnts      ()      const   { return learnts.size(); }
inline int      periplo::CoreSATSolver::nVars         ()      const   { return vardata.size(); }
inline int      periplo::CoreSATSolver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     periplo::CoreSATSolver::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     periplo::CoreSATSolver::setDecisionVar(Var v, bool b)
{ 
	if      ( b && !decision[v]) dec_vars++;
	else if (!b &&  decision[v]) dec_vars--;

	decision[v] = b;
	insertVarOrder(v);
}
inline void     periplo::CoreSATSolver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     periplo::CoreSATSolver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     periplo::CoreSATSolver::interrupt(){ asynch_interrupt = true; }
inline void     periplo::CoreSATSolver::clearInterrupt(){ asynch_interrupt = false; }
inline void     periplo::CoreSATSolver::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     periplo::CoreSATSolver::withinBudget() const {
	return !asynch_interrupt &&
			(conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
			(propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     periplo::CoreSATSolver::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     periplo::CoreSATSolver::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     periplo::CoreSATSolver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     periplo::CoreSATSolver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     periplo::CoreSATSolver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    periplo::CoreSATSolver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     periplo::CoreSATSolver::okay          ()      const   { return ok; }

inline void     periplo::CoreSATSolver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     periplo::CoreSATSolver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     periplo::CoreSATSolver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     periplo::CoreSATSolver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }

//=================================================================================================
// Added Code
#ifdef PRODUCE_PROOF
inline void periplo::CoreSATSolver::checkPartitions( )
{
	if ( config.produce_inter == 0 ) return;

	for (int i = 2; i < nVars(); i++)
	{
		Enode * e = enode_handler->varToEnode( i );
		if ( e->getIPartitions( ) == 0 ) periplo_error2( "Node without partitions: ", e );
		if ( e->getIPartitions( ) % 2 == 1 ) periplo_error2( "Mixed node: ", e );
	}
}
#endif
// Added Code
//=================================================================================================

//=================================================================================================
// Debug etc:

//=================================================================================================
// Added code

inline void periplo::CoreSATSolver::printLit(Lit l)
{
	reportf("%s%-3d", sign(l) ? "-" : "", var(l) );
	//reportf("%s%-3d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}

inline void periplo::CoreSATSolver::printClause( CRef cr ) { printClause (ca[cr]); }

inline void periplo::CoreSATSolver::printClause( ostream & os, CRef cr ) { printClause( os, ca[cr] ); }

inline void periplo::CoreSATSolver::printClause( Clause& c )
{
	for (int i = 0; i < c.size(); i++){
		printLit(c[i]);
		fprintf(stderr, " ");
	}
}

inline void periplo::CoreSATSolver::printClause( ostream & os, Clause& c )
{
	if ( c.size( ) == 0 ) os << "-";
	if ( c.size( ) > 1 ) os << "(or ";
	for (int i = 0; i < c.size(); i++)
	{
		Var v = var(c[i]);
		if ( v <= 1 ) continue;
		Enode * e = enode_handler->varToEnode( v );
		os << (sign(c[i])?"(not ":"") << e << (sign(c[i])?") ":" ");
	}
	if ( c.size( ) > 1 ) os << ")";
}

inline void periplo::CoreSATSolver::printClause( ostream & os, vec< Lit > & c, bool ids )
{
	if ( c.size( ) == 0 ) os << "-";
	if ( c.size( ) > 1 ) os << "(or ";
	for (int i = 0; i < c.size(); i++)
	{
		Var v = var(c[i]);
		if ( v <= 1 ) continue;
		if ( ids )
			os << (sign(c[i])?"-":" ") << v << " ";
		else
		{
			Enode * e = enode_handler->varToEnode( v );
			os << (sign(c[i])?"(not ":"") << e << (sign(c[i])?") ":" ");
		}
	}
	if ( c.size( ) > 1 ) os << ")";
}

inline void periplo::CoreSATSolver::printClause( ostream & os, vector< Lit > & c, bool ids )
{
	if ( c.size( ) == 0 ) os << "-";
	if ( c.size( ) > 1 ) os << "(or ";
	for (size_t i = 0; i < c.size(); i++)
	{
		Var v = var(c[i]);
		if ( v <= 1 ) continue;
		if ( ids )
			os << (sign(c[i])?"-":" ") << v << " ";
		else
		{
			Enode * e = enode_handler->varToEnode( v );
			os << (sign(c[i])?"(not ":"") << e << (sign(c[i])?") ":" ");
		}
	}
	if ( c.size( ) > 1 ) os << ")";
}

inline void periplo::CoreSATSolver::printClause( vec< Lit > & c )
{
	for (int i = 0; i < c.size(); i++){
		printLit(c[i]);
		fprintf(stderr, " ");
	}
}
//=================================================================================================
//=================================================================================================


#endif
