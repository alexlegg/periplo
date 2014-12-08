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

/***************************************************************************************[Solver.cc]
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

#include <math.h>

#include "Sort.h"
#include "CoreSATSolver.h"

//=================================================================================================
// Added Code
namespace periplo
{
extern bool stop;
}

using namespace periplo;
// Added Code
//=================================================================================================

using namespace periplo::minisat;

//=================================================================================================
// Options:

namespace periplo {

static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));

}

//=================================================================================================
// Constructor/Destructor:

//CoreSATSolver::CoreSATSolver() :
CoreSATSolver::CoreSATSolver( Egraph & e, SATConfig & c  )
// Parameters (user settable):
//
: verbosity        (0)
, var_decay        (opt_var_decay)
, clause_decay     (opt_clause_decay)
, random_var_freq  (opt_random_var_freq)
, random_seed      (opt_random_seed)
, luby_restart     (opt_luby_restart)
, ccmin_mode       (opt_ccmin_mode)
, phase_saving     (opt_phase_saving)
, rnd_pol          (false)
, rnd_init_act     (opt_rnd_init_act)
, garbage_frac     (opt_garbage_frac)
, restart_first    (opt_restart_first)
, restart_inc      (opt_restart_inc)

// Parameters (the rest):
//
, learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

// Parameters (experimental):
//
, learntsize_adjust_start_confl (100)
, learntsize_adjust_inc         (1.5)

// Statistics: (formerly in 'SolverStats')
//
, solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
, dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

, ok                 (true)
, cla_inc            (1)
, var_inc            (1)
, watches            (WatcherDeleted(ca))
, qhead              (0)
, simpDB_assigns     (-1)
, simpDB_props       (0)
, order_heap         (VarOrderLt(activity))
, progress_estimate  (0)
, remove_satisfied   (true)

// Resource constraints:
//
, conflict_budget    (-1)
, propagation_budget (-1)
, asynch_interrupt   (false)
//=================================================================================================
// Added Code
#ifdef PRODUCE_PROOF
, proof_                ( new Proof( ca ) )
, proof                 ( * proof_ )
, proof_graph			( NULL )
#endif
, init                  ( false )
, bb_siblings           ( NULL )
, egraph				( e )
, config				( c )
, use_bb_heur			( false )
, learnts_size          ( 0 )
, all_learnts           ( 0 )
// Added Code
//=================================================================================================
{}
//=================================================================================================
// Added Code
void CoreSATSolver::initialize( )
{
	assert( config.isInit( ) );
	assert( !init );

	// TODO check
	/*	restart_first = config.sat_restart_first;
	restart_inc = config.sat_restart_inc;*/
	verbosity = config.verbosity;
	init = true;
}
// Added Code
//=================================================================================================


CoreSATSolver::~CoreSATSolver()
{
	//==================================================================================
	// Added code
#ifdef PRODUCE_PROOF
	// NOTE data already freed in clearDataStructures
#else
	for (int i = 0; i < learnts.size(); i++) ca.free(learnts[i]);
	for (int i = 0; i < clauses.size(); i++) ca.free(clauses[i]);
#endif

	if ( config.produce_stats != 0 ) printStatistics ( config.getStatsOut( ) );
	// NOTE added for convenience
	if ( config.print_stats != 0 ) printStatistics ( cerr );
	delete enode_handler;
	// Added code
	//==================================================================================
}

#ifdef PRODUCE_PROOF
void CoreSATSolver::clearDataStructures()
{
	model.clear();
	conflict.clear();
	activity.clear();
	watches.clear();
	assigns.clear();
	polarity.clear();
	decision.clear();
	vardata.clear();
	trail.clear();
	trail_lim.clear();
	trail_pos.clear();
	assumptions.clear();
	seen.clear();
	analyze_stack.clear();
	analyze_toclear.clear();
	add_tmp.clear();

	for (int i = 0; i < units.size(); i++)   if(units[i] != CRef_Undef)   ca.free(units[i]);
	units.clear();
	for (int i = 0; i < clauses.size(); i++) if(clauses[i] != CRef_Undef) ca.free(clauses[i]);
	clauses.clear();
	for (int i = 0; i < pleaves.size(); i++) if(pleaves[i] != CRef_Undef) ca.free(pleaves[i]);
	pleaves.clear();
	for (int i = 0; i < learnts.size(); i++) if(learnts[i] != CRef_Undef) ca.free(learnts[i]);
	learnts.clear();
	delete proof_;
}
#endif



//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var CoreSATSolver::newVar(bool sign, bool dvar)
{
	int v = nVars();
	watches  .init(mkLit(v, false));
	watches  .init(mkLit(v, true ));
	assigns  .push(l_Undef);
	vardata  .push(mkVarData(CRef_Undef, 0));
	//activity .push(0);
#ifdef PRODUCE_PROOF
	trail_pos .push(-1);
#endif
	activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
	seen     .push(0);
#ifdef PRODUCE_PROOF
	units   .push( CRef_Undef );
#endif
	polarity .push(sign);
	decision .push();
	trail    .capacity(v+1);
	setDecisionVar(v, dvar);

	//==================================================================
	// Added code
	// Skip undo for varTrue and varFalse
	if ( config.incremental )
	{
		if ( v != 0 && v != 1 )
		{
			undo_stack_oper.push_back( NEWVAR );
			undo_stack_elem.push_back( reinterpret_cast< void * >( v ) );
		}
	}
	// Added code
	//==================================================================

	return v;
}


bool CoreSATSolver::addClause_(vec<Lit>& ps
#ifdef PRODUCE_PROOF
		, const ipartitions_t& in
#endif
)
{
	//==================================================================
	// Added code
	// Skip clause if its width is larger than threshold
	// Used to force small width refutations when possible

	if( config.sat_orig_thresh > 0 && ps.size() > config.sat_orig_thresh )
		return true;
	// Added code
	//==================================================================
	assert(decisionLevel() == 0);
#ifdef PRODUCE_PROOF
	assert( in == 0 || ((in & (in - 1)) == 0) );
	bool resolved = false;
	CRef root = CRef_Undef;
#endif
	if (!ok) return false;

	// Check if clause is satisfied and remove false/duplicate literals:
	sort(ps);
	Lit p; int i, j;
#ifdef PRODUCE_PROOF
	root = ca.alloc( ps, false );
	proof.addRoot( root, CLA_ORIG );
	assert( config.isInit( ) );
	if ( config.produce_inter > 0 ) clause_to_partition[ root ] = in;
	proof.beginChain( root );
#endif
	for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
		if (value(ps[i]) == l_True || ps[i] == ~p)
		{
#ifdef PRODUCE_PROOF
			proof.endChain( );
			proof.forceDelete( root );
#endif
			return true;
		}
		else if (value(ps[i]) != l_False && ps[i] != p)
			ps[j++] = p = ps[i];
#ifdef PRODUCE_PROOF
		else if ( value(ps[i]) == l_False )
		{
			resolved = true;
			proof.resolve( units[ var(ps[i]) ], var( ps[i] ) );
		}
#endif
	ps.shrink(i - j);

	if (ps.size() == 0)
	{
#ifdef PRODUCE_PROOF
		proof.endChain( CRef_Undef );
#endif
		return ok = false;
	}

#ifdef PRODUCE_PROOF
	CRef res = CRef_Undef;
	if ( resolved )
	{
		res = ca.alloc( ps, false );
		assert( ca[res].size( ) < ca[root].size( ) );
		proof.endChain( res );
	}
	else
	{
		res = root;
		// Throw away unnecessary chain
		proof.endChain( );
	}
#endif

	if (ps.size() == 1){
#ifdef PRODUCE_PROOF
		assert( res != CRef_Undef );
		assert( units[ var(ps[0]) ] == CRef_Undef );
		units[ var(ps[0]) ] = res;
		if ( config.produce_inter > 0 && var(ps[0]) > 1 ) // Avoids true/false
			units_to_partition.push_back( make_pair( res, in ) );
#endif
		uncheckedEnqueue(ps[0]);
#ifdef PRODUCE_PROOF
		CRef confl = propagate();
		if ( confl == CRef_Undef ) return ok = true;
		return ok = false;
#else
		return ok = (propagate() == CRef_Undef);
#endif
	}else{
#ifdef PRODUCE_PROOF
		CRef cr = res;
#else
		CRef cr = ca.alloc(ps, false);
#endif

#ifdef PRODUCE_PROOF
		if ( config.incremental )
		{
			undo_stack_oper.push_back( NEWPROOF );
			undo_stack_elem.push_back( (void *)cr );
		}

		if ( config.produce_inter > 0 ) clause_to_partition[ cr ] = in;
#endif
		clauses.push(cr);
		attachClause(cr);

		//======================================
		// Added code
		if ( config.incremental )
		{
			undo_stack_oper.push_back( NEWCLAUSE );
			undo_stack_elem.push_back( (void *)cr );
		}
		// Added code
		//======================================
	}
	return true;
}


void CoreSATSolver::attachClause(CRef cr) {
	const Clause& c = ca[cr];
	assert(c.size() > 1);
	watches[~c[0]].push(Watcher(cr, c[1]));
	watches[~c[1]].push(Watcher(cr, c[0]));
	if (c.learnt()) learnts_literals += c.size();
	else            clauses_literals += c.size(); }


void CoreSATSolver::detachClause(CRef cr, bool strict) {
	const Clause& c = ca[cr];
	assert(c.size() > 1);

	if (strict){
		remove(watches[~c[0]], Watcher(cr, c[1]));
		remove(watches[~c[1]], Watcher(cr, c[0]));
	}else{
		// Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
		watches.smudge(~c[0]);
		watches.smudge(~c[1]);
	}

	if (c.learnt()) learnts_literals -= c.size();
	else            clauses_literals -= c.size(); }


void CoreSATSolver::removeClause(CRef cr) {
	Clause& c = ca[cr];
	//==================================================================
	// Added code
	assert( config.isInit( ) );
	if ( config.incremental && detached.find( cr ) != detached.end( ) )
		detached.erase( cr );
	else
		// Added code
		//==================================================================
		detachClause(cr);
	// Don't leave pointers to free'd memory!
	if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
	c.mark(1);
#ifdef PRODUCE_PROOF
	// Remove clause and derivations if ref becomes 0
	// If ref is not 0, we keep it and remove later
	if ( !proof.deletable( cr ) ) pleaves.push( cr );
#else
	ca.free(cr);
#endif
}

bool CoreSATSolver::satisfied(const Clause& c) const {
	for (int i = 0; i < c.size(); i++)
		if (value(c[i]) == l_True)
			return true;
	return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void CoreSATSolver::cancelUntil(int level) {
	if (decisionLevel() > level){
		for (int c = trail.size()-1; c >= trail_lim[level]; c--){
			Var      x  = var(trail[c]);
			assigns [x] = l_Undef;
			if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
				polarity[x] = sign(trail[c]);
			insertVarOrder(x); }
		qhead = trail_lim[level];
		trail.shrink(trail.size() - trail_lim[level]);
		trail_lim.shrink(trail_lim.size() - level);
	} }


//=================================================================================================
// Added Code

void CoreSATSolver::addNewAtom( Enode * e )
{
	assert( e );
	assert( !e->isTrue ( ) );
	assert( !e->isFalse( ) );
	// Automatically adds new variable for e
	Lit l = enode_handler->enodeToLit( e );
}

// Added by Grisha
void CoreSATSolver::addBB(vec<Var>& vs) {
	use_bb_heur = true;
	vec<Var>* out = new vec<Var>();
	for (int i = 0; i < vs.size(); i++) {
		Var v = vs[i];
		out->push(v);
		assert(v < nVars());
		// TODO check replacement - assert(!bb_vars.contains(v));
		assert(!bb_vars.has(v));
		bb_vars.insert(v, out);
	}
}

void CoreSATSolver::cancelUntilVar( Var v )
{
	int c;
	for ( c = trail.size( )-1 ; var(trail[ c ]) != v ; c -- )
	{
		Var     x    = var(trail[ c ]);
		assigns[ x ] = l_Undef;
		insertVarOrder( x );
	}

	// Reset v itself
	assigns[ v ] = l_Undef;
	insertVarOrder( v );

	trail.shrink(trail.size( ) - c );
	qhead = trail.size( );

	if ( decisionLevel( ) > level( v ) )
	{
		assert( c > 0 );
		assert( c - 1 < trail.size( ) );
		assert( var(trail[ c ]) == v );

		int lev = level( var(trail[ c-1 ]) );
		assert( lev < trail_lim.size( ) );

		trail_lim[ lev ] = c;
		trail_lim.shrink(trail_lim.size( ) - lev);
	}
}

void CoreSATSolver::cancelUntilVarTempInit( Var v )
{
	int c;
	for ( c = trail.size( )-1 ; var(trail[ c ]) != v ; c -- )
	{
		Lit p = trail[ c ];
		Var x = var( p );
		lit_to_restore.push( p );
		val_to_restore.push( assigns[ x ] );
		assigns[ x ] = l_Undef;
	}
	// Stores v as well
	Lit p = trail[ c ];
	Var x = var( p );
	assert( v == x );
	lit_to_restore.push( p );
	val_to_restore.push( assigns[ x ] );
	assigns[ x ] = l_Undef;

	// Reset v itself
	assigns[ v ] = l_Undef;

	trail.shrink(trail.size( ) - c );
}

void CoreSATSolver::cancelUntilVarTempDone( )
{
	while ( val_to_restore.size( ) > 0 )
	{
		Lit p = lit_to_restore.last( );
		Var x = var( p );
		lit_to_restore.pop( );
		lbool v = val_to_restore.last( );
		val_to_restore.pop( );
		assigns[ x ] = v;
		trail.push( p );
	}
}
// Added Code
//=================================================================================================

//=================================================================================================
// Major methods:


Lit CoreSATSolver::pickBranchLit()
{
	Var next = var_Undef;

	// Random decision:
	if (drand(random_seed) < random_var_freq && !order_heap.empty()){
		next = order_heap[irand(random_seed,order_heap.size())];
		if (value(next) == l_Undef && decision[next])
			rnd_decisions++; }

	//==========================================================================
	// Added code
	// Added by Grisha
	// the bit blasted literal mode
	if ((use_bb_heur) && (bb_siblings != NULL)) {
		for (int i = 0; i < bb_siblings->size(); i++) {
			Var v = (*bb_siblings)[i];
			if ( (assigns[v] == l_Undef) && decision[v]) {
				next = v;
				break;
			}
		}
		if (next == var_Undef) bb_siblings = NULL; // All bb lits have a value
	}
	// Added code
	//==========================================================================

	// Activity based decision:
	while (next == var_Undef || value(next) != l_Undef || !decision[next])
		if (order_heap.empty()){
			next = var_Undef;
			break;
		}else
			next = order_heap.removeMin();

	//=======================================================================================================
	// Added code
	// Added by Grisha
	if ( next == var_Undef ) return lit_Undef;
	// TODO check replacement of "contains" with "has"
	if ((use_bb_heur) && (bb_vars.has(next))) bb_siblings = bb_vars[next];
	// Added code
	//=======================================================================================================

	return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}

#ifdef PRODUCE_PROOF
class lastToFirst_lt {  // Helper class to 'analyze' -- order literals from last to first occurrence in 'trail[]'.
	const vec<int>& trail_pos;
public:
	lastToFirst_lt(const vec<int>& t) : trail_pos(t) {}
	bool operator () (Lit p, Lit q) { return trail_pos[var(p)] > trail_pos[var(q)]; }
};
#endif


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void CoreSATSolver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
#ifdef PRODUCE_PROOF
	assert( proof.notBegun( ) );
#endif

	int pathC = 0;
	Lit p     = lit_Undef;

	// Generate conflict clause:
	//
	out_learnt.push();      // (leave room for the asserting literal)
	int index   = trail.size() - 1;

#ifdef PRODUCE_PROOF
	proof.beginChain( confl );
#endif

	do{
		assert(confl != CRef_Undef); // (otherwise should be UIP)
		Clause& c = ca[confl];

		if (c.learnt())
			claBumpActivity(c);

		for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
			Lit q = c[j];

			if (!seen[var(q)] && level(var(q)) > 0){
				varBumpActivity(var(q));
				seen[var(q)] = 1;
				if (level(var(q)) >= decisionLevel())
					pathC++;
				else
					out_learnt.push(q);
			}
#ifdef PRODUCE_PROOF
			else if( !seen[var(q)] )
			{
				if ( level(var(q)) == 0 ) proof.resolve( units[ var( q ) ], var( q ) );
			}
#endif
		}

		// Select next clause to look at:
		while (!seen[var(trail[index--])]);
		p     = trail[index+1];
		confl = reason(var(p));
		seen[var(p)] = 0;
		pathC--;

#ifdef PRODUCE_PROOF
		if ( pathC > 0 ) proof.resolve( confl, var( p ) );
#endif

	}while (pathC > 0);
	out_learnt[0] = ~p;

	// Simplify conflict clause:
	//
	int i, j;
	out_learnt.copyTo(analyze_toclear);
	if (ccmin_mode == 2){
		uint32_t abstract_level = 0;
		for (i = 1; i < out_learnt.size(); i++)
			abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)
#ifdef PRODUCE_PROOF
		analyze_proof.clear( );
#endif
		for (i = j = 1; i < out_learnt.size(); i++)
			if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
				out_learnt[j++] = out_learnt[i];

	}else if (ccmin_mode == 1){
#ifdef PRODUCE_PROOF
		// FIXME
		periplo_error( "learnt clauses local minimization not yet handled in proofs" );
#endif
		for (i = j = 1; i < out_learnt.size(); i++)
		{
			Var x = var(out_learnt[i]);

			if (reason(x) == CRef_Undef)
				out_learnt[j++] = out_learnt[i];
			else
			{
				Clause& c = ca[reason(var(out_learnt[i]))];
				for (int k = 1; k < c.size(); k++)
					if (!seen[var(c[k])] && level(var(c[k])) > 0){
						out_learnt[j++] = out_learnt[i];
						break; }
			}
		}
	}else
		i = j = out_learnt.size();

	max_literals += out_learnt.size();
	out_learnt.shrink(i - j);
	tot_literals += out_learnt.size();

	// Find correct backtrack level:
	//
	if (out_learnt.size() == 1)
		out_btlevel = 0;
	else{
		int max_i = 1;
		// Find the first literal assigned at the next-highest level:
		for (int i = 2; i < out_learnt.size(); i++)
			if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
				max_i = i;
		// Swap-in this literal at index 1:
		Lit p             = out_learnt[max_i];
		out_learnt[max_i] = out_learnt[1];
		out_learnt[1]     = p;
		out_btlevel       = level(var(p));
	}

#ifdef PRODUCE_PROOF
	// Finalize proof logging with conflict clause recursive minimization
	// First sort with respect to trail position
	sort( analyze_proof, lastToFirst_lt(trail_pos) );
	for ( int k = 0 ; k < analyze_proof.size() ; k++ )
	{
		Var v = var( analyze_proof[ k ] );
		assert( level(v) > 0 );
		//cerr << "Adding " << v << " level " << level(v) << "  var" << endl;
		CRef c = reason( v );
		// Cannot be a decision variable
		assert( c != CRef_Undef );
		proof.resolve( c, v );
		// Look for level 0 unit clauses
		Clause& cla = ca[ c ];
		for (int k = 1; k < cla.size(); k++)
		{
			Var vv = var(cla[k]);
			if (level( vv ) == 0) proof.resolve( units[ vv ], vv );
		}
	}
	// Chain will be ended outside analyze
#endif

	for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool CoreSATSolver::litRedundant(Lit p, uint32_t abstract_levels)
{
	analyze_stack.clear(); analyze_stack.push(p);
	int top = analyze_toclear.size();
#ifdef PRODUCE_PROOF
	int top2 = analyze_proof.size();
#endif
	while (analyze_stack.size() > 0){
		assert(reason(var(analyze_stack.last())) != CRef_Undef);
		Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

		for (int i = 1; i < c.size(); i++){
			Lit p  = c[i];
			if (!seen[var(p)] && level(var(p)) > 0)
			{
				if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0)
				{
					seen[var(p)] = 1;
					analyze_stack.push(p);
					analyze_toclear.push(p);
#ifdef PRODUCE_PROOF
					// Keep track of covered literals in the implication graph
					// No level 0 units nor decision variables
					analyze_proof.push( p );
#endif
				}
				else{
					for (int j = top; j < analyze_toclear.size(); j++)
						seen[var(analyze_toclear[j])] = 0;
					analyze_toclear.shrink(analyze_toclear.size() - top);
#ifdef PRODUCE_PROOF
					// Remove literals added during this call of litRedundant
					analyze_proof.shrink(analyze_proof.size() - top2);
#endif
					return false;
				}
			}
		}
	}
#ifdef PRODUCE_PROOF
	analyze_proof.push( p );
#endif
	return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void CoreSATSolver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
#ifdef PRODUCE_PROOF
	periplo_error( "analyzeFinal not handled (yet) in proofs" );
#endif
	out_conflict.clear();
	out_conflict.push(p);

	if (decisionLevel() == 0)
		return;

	seen[var(p)] = 1;

	for (int i = trail.size()-1; i >= trail_lim[0]; i--){
		Var x = var(trail[i]);
		if (seen[x]){
			if (reason(x) == CRef_Undef){
				assert(level(x) > 0);
				out_conflict.push(~trail[i]);
			}else{
				Clause& c = ca[reason(x)];
				for (int j = 1; j < c.size(); j++)
					if (level(var(c[j])) > 0)
						seen[var(c[j])] = 1;
			}
			seen[x] = 0;
		}
	}

	seen[var(p)] = 0;
}


void CoreSATSolver::uncheckedEnqueue(Lit p, CRef from)
{
	assert(value(p) == l_Undef);
	assigns[var(p)] = lbool(!sign(p));
	vardata[var(p)] = mkVarData(from, decisionLevel());
	trail.push_(p);
#ifdef PRODUCE_PROOF
	trail_pos[var(p)] = trail.size();
#endif
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/


CRef CoreSATSolver::propagate()
{
	CRef    confl     = CRef_Undef;
	int     num_props = 0;
	watches.cleanAll();

	while (qhead < trail.size()){
		Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
		vec<Watcher>&  ws  = watches[p];
		Watcher        *i, *j, *end;
		num_props++;

		//=================================================================================================
		// Added Code
		if( config.sat_propagate_small > 0 )
		{
			// Sort watcher vector according to clauses size
			// NOTE try to propagate first smaller clause, hoping to get a smaller proof
			/*	for (int i = (ws.size() - 1); i > 0; i--)
			{
				for (int j = 1; j <= i; j++)
				{
					if (ca[ws[j-1].cref].size() > ca[ws[j].cref].size())
					{
						Watcher temp = ws[j-1];
						ws[j-1] = ws[j];
						ws[j] = temp;
					}
				}
			}*/
			sort(ws, watcher_lt(ca));
			//for(int i=0; i < ws.size() - 1; i++ ) assert( ca[ws[i].cref].size() <= ca[ws[i+1].cref].size() );
		}
		// Added Code
		//=================================================================================================

		for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
			// Try to avoid inspecting the clause:
			Lit blocker = i->blocker;
			if (value(blocker) == l_True){
				*j++ = *i++; continue; }

			// Make sure the false literal is data[1]:
			CRef     cr        = i->cref;
			Clause&  c         = ca[cr];
			Lit      false_lit = ~p;
			if (c[0] == false_lit)
				c[0] = c[1], c[1] = false_lit;
			assert(c[1] == false_lit);
			i++;

			// If 0th watch is true, then clause is already satisfied.
			Lit     first = c[0];
			Watcher w     = Watcher(cr, first);
			if (first != blocker && value(first) == l_True){
				*j++ = w; continue; }

			// Look for new watch:
			for (int k = 2; k < c.size(); k++)
				if (value(c[k]) != l_False){
					c[1] = c[k]; c[k] = false_lit;
					watches[~c[1]].push(w);
					goto NextClause; }

#ifdef PRODUCE_PROOF
			// Did not find watch -- clause is unit under assignment:
			if ( decisionLevel() == 0 )
			{
				proof.beginChain( cr );
				for (int k = 1; k < c.size(); k++)
				{
					assert( level( var(c[k]) ) == 0 );
					proof.resolve( units[var(c[k])], var(c[k]) );
				}
				// (if variable already has 'id', it must be with the other polarity
				// and we should have derived the empty clause here)
				assert( units[ var(first) ] == CRef_Undef || value( first ) == l_False );
				if ( value(first) != l_False )
				{
					vec< Lit > tmp;
					tmp.push( first );
					CRef uc = ca.alloc( tmp );
					proof.endChain( uc );
					assert( units[ var(first) ] == CRef_Undef );
					units[ var(first) ] = uc;
				}
				else
				{
					vec< Lit > tmp;
					tmp.push( first );
					CRef uc = ca.alloc( tmp );
					proof.endChain( uc );
					pleaves.push( uc );
					// Empty clause derived:
					proof.beginChain( units[ var(first) ] );
					proof.resolve( uc, var(first) );
					proof.endChain( CRef_Undef );
				}
			}
#endif

			// Did not find watch -- clause is unit under assignment:
			*j++ = w;
			if (value(first) == l_False){
				confl = cr;
				qhead = trail.size();
				// Copy the remaining watches:
				while (i < end)
					*j++ = *i++;
			}else
				uncheckedEnqueue(first, cr);

			NextClause:;
		}
		ws.shrink(i - j);
	}
	propagations += num_props;
	simpDB_props -= num_props;

	return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt {
	ClauseAllocator& ca;
	reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
	bool operator () (CRef x, CRef y) {
		return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); }
};
void CoreSATSolver::reduceDB()
{
	int     i, j;
	double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

	sort(learnts, reduceDB_lt(ca));
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++){
		Clause& c = ca[learnts[i]];
		if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
			removeClause(learnts[i]);
		else
			learnts[j++] = learnts[i];
	}
	learnts.shrink(i - j);
	checkGarbage();

#ifdef PRODUCE_PROOF
	// Remove unused leaves
	for ( i = j = 0 ; i < pleaves.size( ) ; i++ )
	{
		CRef cr = pleaves[i];
		assert(ca[cr].mark() == 1);
		if ( ! proof.deletable( cr ) ) pleaves[j++] = pleaves[i];
	}
	pleaves.shrink(i - j);
#endif
}


void CoreSATSolver::removeSatisfied(vec<CRef>& cs)
{
	int i, j;
	for (i = j = 0; i < cs.size(); i++){
		Clause& c = ca[cs[i]];
		if (satisfied(c))
			removeClause(cs[i]);
		else
			cs[j++] = cs[i];
	}
	cs.shrink(i - j);
}


void CoreSATSolver::rebuildOrderHeap()
{
	vec<Var> vs;
	for (Var v = 0; v < nVars(); v++)
		if (decision[v] && value(v) == l_Undef)
			vs.push(v);
	order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool CoreSATSolver::simplify()
{
	assert(decisionLevel() == 0);

	if (!ok || propagate() != CRef_Undef)
		return ok = false;

	if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
		return true;

	// Remove satisfied clauses:
	removeSatisfied(learnts);
	if (remove_satisfied)        // Can be turned off.
		removeSatisfied(clauses);
	checkGarbage();
	rebuildOrderHeap();

	simpDB_assigns = nAssigns();
	simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

	return true;
}

//=================================================================================================
// Added Code

void CoreSATSolver::printStatistics( ostream & os )
{
	os << "# -------------------------" << endl;
	os << "# STATISTICS FOR SAT SOLVER" << endl;
	os << "# -------------------------" << endl;
	os << "# Restarts.................: " << starts << endl;
	os << "# Conflicts................: " << conflicts << endl;
	os << "# Decisions................: " << (float)decisions << endl;
	os << "# Propagations.............: " << propagations << endl;
	os << "# Conflict literals........: " << tot_literals << endl;
	os << "# Conflicts learnt.........: " << all_learnts << endl;
	os << "# Average learnts size.....: " << learnts_size/all_learnts << endl;
	if ( config.sat_preprocess_booleans != 0 ) os << "# Preprocessing time.......: " << preproc_time << " s" << endl;
}

// TODO to be restored
void CoreSATSolver::pushBacktrackPoint( )
{
	/*
	assert( config.incremental );
	//
	// Save undo stack size
	//
	assert( undo_stack_oper.size( ) == undo_stack_elem.size( ) );
	undo_stack_size.push_back( undo_stack_oper.size( ) );
	undo_trail_size.push_back( trail.size( ) );
#ifdef PRODUCE_PROOF
	proof.pushBacktrackPoint( );
#endif
	 */
}

// TODO to be restored
void CoreSATSolver::popBacktrackPoint ( )
{
	/*
	assert( config.incremental );
	//
	// Force restart, but retain assumptions
	//
	cancelUntil(0);
	//
	// Shrink back trail
	//
	int new_trail_size = undo_trail_size.back( );
	undo_trail_size.pop_back( );
	for ( int i = trail.size( ) - 1 ; i >= new_trail_size ; i -- )
	{
		Var     x  = var(trail[i]);
		assigns[x] = l_Undef;
		setReason(x, CRef_Undef);
		insertVarOrder(x);
	}
	trail.shrink(trail.size( ) - new_trail_size);
	assert( trail_lim.size( ) == 0 );
	qhead = trail.size( );
	//
	// Undo operations
	//
	size_t new_stack_size = undo_stack_size.back( );
	undo_stack_size.pop_back( );
	while ( undo_stack_oper.size( ) > new_stack_size )
	{
		const oper_t op = undo_stack_oper.back( );

		if ( op == NEWVAR )
		{
#ifdef BUILD_64
			long xl = reinterpret_cast< long >( undo_stack_elem.back( ) );
			const Var x = static_cast< Var >( xl );
#else
			const Var x = reinterpret_cast< int >( undo_stack_elem.back( ) );
#endif

			// Undoes insertVarOrder( )
			assert( order_heap.inHeap(x) );
			// FIXME this method does not exist anymore
			//order_heap  .remove(x);
			// Undoes decision_var ... watches
			decision    .pop();
			polarity    .pop();
			seen        .pop();
			activity    .pop();
			// FIXME this data structure does not exist anymore
			//level       .pop();
			assigns     .pop();
			reason      .pop();
			watches     .pop();
			watches     .pop();
			// Remove variable from translation tables
			enode_handler->clearVar( x );
		}
		else if ( op == NEWUNIT )
			; // Do nothing
		else if ( op == NEWCLAUSE )
		{
			Clause * c = (Clause *)undo_stack_elem.back( );
			assert( clauses.last( ) == c );
			clauses.pop( );
			removeClause( *c );
		}
		else if ( op == NEWLEARNT )
		{
			Clause * c = (Clause *)undo_stack_elem.back( );
			detachClause( *c );
			detached.insert( c );
		}
#ifdef PRODUCE_PROOF
		else if ( op == NEWPROOF )
		{
			assert( false );
		}
#endif
		else
		{
			periplo_error2( "unknown undo operation in CoreSATSolver", op );
		}

		undo_stack_oper.pop_back( );
		undo_stack_elem.pop_back( );
	}

	assert( undo_stack_elem.size( ) == undo_stack_oper.size( ) );
#ifdef PRODUCE_PROOF
	proof.popBacktrackPoint( );
#endif
	// Restore OK
	restoreOK( );
	assert( isOK( ) );
	 */
}

// TODO to be restored
void CoreSATSolver::reset( )
{
	/*
	assert( config.incremental );
	//
	// Force restart, but retain assumptions
	//
	cancelUntil(0);
	//
	// Shrink back trail
	//
	undo_trail_size.clear( );
	int new_trail_size = 0;
	for ( int i = trail.size( ) - 1 ; i >= new_trail_size ; i -- )
	{
		Var     x  = var(trail[i]);
		assigns[x] = toInt(l_Undef);
		reason [x] = NULL;
		insertVarOrder(x);
	}
	trail.shrink(trail.size( ) - new_trail_size);
	assert( trail_lim.size( ) == 0 );
	qhead = trail.size( );
	//
	// Undo operations
	//
	while ( undo_stack_oper.size( ) > 0 )
	{
		const oper_t op = undo_stack_oper.back( );

		if ( op == NEWVAR )
		{
#ifdef BUILD_64
			long xl = reinterpret_cast< long >( undo_stack_elem.back( ) );
			const Var x = static_cast< Var >( xl );
#else
			const Var x = reinterpret_cast< int >( undo_stack_elem.back( ) );
#endif

			// Undoes insertVarOrder( )
			assert( order_heap.inHeap(x) );
			order_heap  .remove(x);
			// Undoes decision_var ... watches
			decision_var.pop();
			polarity    .pop();
			seen        .pop();
			activity    .pop();
			level       .pop();
			assigns     .pop();
			reason      .pop();
			watches     .pop();
			watches     .pop();
			// Remove variable from translation tables
			enode_handler->clearVar( x );
		}
		else if ( op == NEWUNIT )
			; // Do nothing
		else if ( op == NEWCLAUSE )
		{
			Clause * c = (Clause *)undo_stack_elem.back( );
			assert( clauses.last( ) == c );
			clauses.pop( );
			removeClause( *c );
		}
		else if ( op == NEWLEARNT )
		{
			Clause * c = (Clause *)undo_stack_elem.back( );
			removeClause( *c );
		}
#ifdef PRODUCE_PROOF
		else if ( op == NEWPROOF )
		{
			assert( false );
		}
#endif
		else
		{
			periplo_error2( "unknown undo operation in CoreSATSolver", op );
		}

		undo_stack_oper.pop_back( );
		undo_stack_elem.pop_back( );
	}
	//
	// Clear all learnts
	//
	while( learnts.size( ) > 0 )
	{
		Clause * c = learnts.last( );
		learnts.pop( );
		removeClause( *c );
	}
#ifdef PRODUCE_PROOF
	proof.reset( );
#endif
	assert( undo_stack_elem.size( ) == undo_stack_oper.size( ) );
	assert( learnts.size( ) == 0 );
	 */
}

lbool CoreSATSolver::getModel( Enode * atom )
{
	assert( atom->isAtom() );
	Var v = enode_handler->enodeToVar( atom );
	//assert( model[ v ] != l_Undef );
	return model[ v ];
}
// Added Code
//=================================================================================================

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool CoreSATSolver::search(int nof_conflicts)
{
	assert(ok);
	int         backtrack_level;
	int         conflictC = 0;
	vec<Lit>    learnt_clause;
	starts++;

	for (;;){

		// Added line
		if ( periplo::stop ) return l_Undef;

		CRef confl = propagate();
		if (confl != CRef_Undef)
		{
			// CONFLICT
			conflicts++; conflictC++;
			if (decisionLevel() == 0) return l_False;

			learnt_clause.clear();
			analyze(confl, learnt_clause, backtrack_level);
			cancelUntil(backtrack_level);

			if (learnt_clause.size() == 1)
			{
				uncheckedEnqueue(learnt_clause[0]);
#ifdef PRODUCE_PROOF
				CRef cr = ca.alloc( learnt_clause, false );
				proof.endChain( cr );
				assert( units[ var(learnt_clause[0]) ] == CRef_Undef );
				units[ var(learnt_clause[0]) ] = proof.last( );
#endif
			}
			else
			{
#ifdef PRODUCE_PROOF
				if (config.sat_restart_learnt_thresh > 0 && learnt_clause.size() > config.sat_restart_learnt_thresh)
				{
					//std::cout << "Restarting since learnt size is " << learnt_clause.size() << std::endl;
					proof.endChain();
					varDecayActivity();
					claDecayActivity();
					cancelUntil(0);
					return l_Undef;
				}
#endif
				//=====================================
				// Added code
				learnts_size += learnt_clause.size( );
				all_learnts ++;
				// Added code
				//=====================================
				CRef cr = ca.alloc(learnt_clause, true);
#ifdef PRODUCE_PROOF
				proof.endChain( cr );
				if ( config.incremental )
				{
					undo_stack_oper.push_back( NEWPROOF );
					undo_stack_elem.push_back( (void *)cr );
				}
#endif
				learnts.push(cr);
				//=====================================
				// Added code
				if ( config.incremental )
				{
					undo_stack_oper.push_back( NEWLEARNT );
					undo_stack_elem.push_back( (void *)cr );
				}
				// Added code
				//=====================================
				attachClause(cr);
				claBumpActivity(ca[cr]);
				uncheckedEnqueue(learnt_clause[0], cr);
			}

			varDecayActivity();
			claDecayActivity();

			if (--learntsize_adjust_cnt == 0){
				learntsize_adjust_confl *= learntsize_adjust_inc;
				learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
				max_learnts             *= learntsize_inc;

				if (verbosity >= 1)
					printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
							(int)conflicts,
							(int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
							(int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
			}

		}
		else
		{
			// NO CONFLICT
			if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget())
			{
				// Reached bound on number of conflicts:
				progress_estimate = progressEstimate();
				cancelUntil(0);
				return l_Undef;
			}

			// Simplify the set of problem clauses:
			if (decisionLevel() == 0 && !simplify())
				return l_False;

			if (learnts.size()-nAssigns() >= max_learnts)
				// Reduce the set of learnt clauses:
				reduceDB();

			Lit next = lit_Undef;
			while (decisionLevel() < assumptions.size())
			{
				// Perform user provided assumption:
				Lit p = assumptions[decisionLevel()];
				if (value(p) == l_True){
					// Dummy decision level:
					newDecisionLevel();
				}else if (value(p) == l_False){
					analyzeFinal(~p, conflict);
					return l_False;
				}else{
					next = p;
					break;
				}
			}

			if (next == lit_Undef)
			{
				// New variable decision:
				decisions++;
				next = pickBranchLit();

				if (next == lit_Undef)
					// Model found:
					return l_True;
			}

			// Increase decision level and enqueue 'next'
			newDecisionLevel();
			uncheckedEnqueue(next);
		}
	}
}


double CoreSATSolver::progressEstimate() const
{
	double  progress = 0;
	double  F = 1.0 / nVars();

	for (int i = 0; i <= decisionLevel(); i++){
		int beg = i == 0 ? 0 : trail_lim[i - 1];
		int end = i == decisionLevel() ? trail.size() : trail_lim[i];
		progress += pow(F, i) * (end - beg);
	}

	return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

	// Find the finite subsequence that contains index 'x', and the
	// size of that subsequence:
	int size, seq;
	for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

	while (size-1 != x){
		size = (size-1)>>1;
		seq--;
		x = x % size;
	}

	return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool CoreSATSolver::solve_()
{
	//=================================================================================================
	// Added Code
	assert( init );
	// Check some invariants before we start ...
	assert( config.logic != UNDEF );
#ifdef PRODUCE_PROOF
	// Checks that every variable is associated to a non-zero partition
	if( config.produce_inter > 0 ) checkPartitions( );
#endif
	if ( config.sat_dump_cnf != 0 ) dumpCNF( );
	if ( config.sat_dump_rnd_inter != 0 ) dumpRndInter( );

	//cout << "Number of clauses: " << clauses.size() << endl;

	// Added Code
	//=================================================================================================

	model.clear();
	conflict.clear();
	if (!ok) return l_False;

	solves++;

	max_learnts               = nClauses() * learntsize_factor;
	learntsize_adjust_confl   = learntsize_adjust_start_confl;
	learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
	lbool   status            = l_Undef;

	if (verbosity >= 1){
		printf("============================[ Search Statistics ]==============================\n");
		printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
		printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
		printf("===============================================================================\n");
	}

	// Search:
	int curr_restarts = 0;
	//=================================================================================================
	// Added Code
	while (status == l_Undef && !periplo::stop){
		// Added Code
		//=================================================================================================
		//while (status == l_Undef){
		double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
		status = search(rest_base * restart_first);
		if (!withinBudget()) break;
		curr_restarts++;
	}

	if (verbosity >= 1)
		printf("===============================================================================\n");

	if (status == l_True){
		// Extend & copy model:
		model.growTo(nVars());
		for (int i = 0; i < nVars(); i++) model[i] = value(i);
		//==============================================================
		// Added code
		// TODO restore
		// verifyModel( );
		// Compute models
		if ( config.produce_models && !config.incremental )
		{
			egraph.computeModel( );
			printModel( );
		}
		// Added code
		//==============================================================
		//}else if (status == l_False && conflict.size() == 0)
	}else{
		//==============================================================
		// Added code
		assert( periplo::stop || status == l_False);
		if (conflict.size() == 0)
			// Added code
			//==============================================================
			ok = false;
	}
	//==============================================================
	// Added code
	// We terminate
	// TODO does this still make sense?
	//if ( !config.incremental ) cancelUntil(-1);
	// We return to level 0, ready to accept new clauses
	//else
	// Added code
	//==============================================================
	cancelUntil(0);

	return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
	if (map.size() <= x || map[x] == -1){
		map.growTo(x+1, -1);
		map[x] = max++;
	}
	return map[x];
}


void CoreSATSolver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
	if (satisfied(c)) return;

	for (int i = 0; i < c.size(); i++)
		if (value(c[i]) != l_False)
			fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
	fprintf(f, "0\n");
}


void CoreSATSolver::toDimacs(const char *file, const vec<Lit>& assumps)
{
	FILE* f = fopen(file, "wr");
	if (f == NULL)
		fprintf(stderr, "could not open file %s\n", file), exit(1);
	toDimacs(f, assumps);
	fclose(f);
}


void CoreSATSolver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
	// Handle case when solver is in contradictory state:
	if (!ok){
		fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
		return; }

	vec<Var> map; Var max = 0;

	// Cannot use removeClauses here because it is not safe
	// to deallocate them at this point. Could be improved.
	int cnt = 0;
	for (int i = 0; i < clauses.size(); i++)
		if (!satisfied(ca[clauses[i]]))
			cnt++;

	for (int i = 0; i < clauses.size(); i++)
		if (!satisfied(ca[clauses[i]])){
			Clause& c = ca[clauses[i]];
			for (int j = 0; j < c.size(); j++)
				if (value(c[j]) != l_False)
					mapVar(var(c[j]), map, max);
		}

	// Assumptions are added as unit clauses:
	cnt += assumptions.size();

	fprintf(f, "p cnf %d %d\n", max, cnt);

	for (int i = 0; i < assumptions.size(); i++){
		assert(value(assumptions[i]) != l_False);
		fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
	}

	for (int i = 0; i < clauses.size(); i++)
		toDimacs(f, ca[clauses[i]], map, max);

	if (verbosity > 0)
		printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void CoreSATSolver::relocAll(ClauseAllocator& to)
{
	// All watchers:
	//
	// for (int i = 0; i < watches.size(); i++)
	watches.cleanAll();
	for (int v = 0; v < nVars(); v++)
		for (int s = 0; s < 2; s++){
			Lit p = mkLit(v, s);
			// printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
			vec<Watcher>& ws = watches[p];
			for (int j = 0; j < ws.size(); j++)
				ca.reloc(ws[j].cref, to);
		}

	// All reasons:
	//
	for (int i = 0; i < trail.size(); i++){
		Var v = var(trail[i]);

		if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
			ca.reloc(vardata[v].reason, to);
	}

	// All learnt:
	//
	for (int i = 0; i < learnts.size(); i++)
		ca.reloc(learnts[i], to);

	// All original:
	//
	for (int i = 0; i < clauses.size(); i++)
		ca.reloc(clauses[i], to);
}


void CoreSATSolver::garbageCollect()
{
	// Initialize the next region to a size corresponding to the estimated utilization degree. This
	// is not precise but should avoid some unnecessary reallocations for the new region:
	ClauseAllocator to(ca.size() - ca.wasted());

	relocAll(to);
	if (verbosity >= 2)
		printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
				ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
	to.moveTo(ca);
}
