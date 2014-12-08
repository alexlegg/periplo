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

#ifndef SATConfig_H
#define SATConfig_H

#include "Global.h"
#include "SolverTypes.h"

namespace periplo {
//
// Holds informations about the configuration of the solver
//
struct SATConfig
{
  //
  // For standard executable
  //
  SATConfig ( int    argc
	    , char * argv[ ] )
    : filename ( argv[ argc - 1 ] )
    , rocset   ( false )
    , docset   ( false )
  {
    initializeConfig( );
    // Parse command-line options
    parseCMDLine( argc, argv );
  }
  //
  // For API
  //
  SATConfig ( )
    : filename ( NULL )
    , rocset   ( false )
    , docset   ( false )
  {
    initializeConfig( );
  }

  ~SATConfig ( )
  { 
    if ( produce_stats )  stats_out.close( );
    if ( rocset )         out.close( );
    if ( docset )         err.close( );
  }

  void initializeConfig ( );

  void parseConfig      ( char * );
  void parseCMDLine     ( int argc, char * argv[ ] );
  void printHelp        ( );
  void printConfig      ( ostream & out );

  inline bool      isInit      ( ) { return logic != UNDEF; }

  inline ostream & getStatsOut     ( ) { assert( produce_stats );  return stats_out; }
  inline ostream & getRegularOut   ( ) { return rocset ? out : cout; }
  inline ostream & getDiagnosticOut( ) { return docset ? err : cerr; }

  inline void setProduceModels( ) { if ( produce_models != 0 ) return; produce_models = 1; }  
  inline void setProduceProofs( ) { if ( print_proofs_smtlib2 != 0 ) return; print_proofs_smtlib2 = 1; }
  inline void setProduceInter( )  { if ( produce_inter != 0 ) return; produce_inter = 1; }

  inline void setRegularOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stdout" ) != 0 && !rocset )
    {
      out.open( attr );
      if( !out ) 
	periplo_error2( "can't open ", attr );
      rocset = true;
    }
  }

  inline void setDiagnosticOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stderr" ) != 0 && !rocset )
    {
      err.open( attr );
      if( !err ) 
	periplo_error2( "can't open ", attr );
      rocset = true;
    }
  }

  const char * filename;                     // Holds the name of the input filename
  logic_t      logic;                        // SMT-Logic under consideration
  periplo::minisat::lbool status;                       // Status of the benchmark
  int          incremental;                  // Incremental solving
  int          produce_stats;                // Should print statistics ?
  int          print_stats;                  // Should print statistics ?
  int          produce_models;               // Should produce models ?
  bool         rocset;                       // Regular Output Channel set ?
  bool         docset;                       // Diagnostic Output Channel set ?
  int          dump_formula;                 // Dump input formula
  int          verbosity;                    // Verbosity level
  bool         print_success;                // Print sat/unsat
  int          certification_level;          // Level of certification
  char         certifying_solver[256];       // Executable used for certification
  // SAT-Solver related parameters
  int          sat_restart_first;            // First limit of restart
  double       sat_restart_inc;              // Increment of limit
  int          sat_use_luby_restart;         // Use luby restart mechanism
  int          sat_learn_up_to_size;         // Learn theory clause up to size
  int          sat_temporary_learn;          // Is learning temporary
  int          sat_preprocess_booleans;      // Activate satelite (on booleans)
  int          sat_centrality;               // Specify centrality parameter
  int          sat_trade_off;                // Specify trade off
  int          sat_minimize_conflicts;       // Conflict minimization: 0 none, 1 yes
  int          sat_dump_cnf;                 // Dump cnf formula
  int          sat_dump_rnd_inter;           // Dump random interpolant
  int		   sat_propagate_small;			 // Try to propagate first smaller clauses
  int		   sat_restart_learnt_thresh;    // Restart solver if the current learnt has width > thresh
  int		   sat_orig_thresh;				 // Allows original clauses of width up to thresh
  // Proof manipulation parameters
  int          print_proofs_smtlib2;         // Should print proofs ?
  int 	       print_proofs_dotty;	         // Should print proofs ?
  int          produce_inter;                // Should produce interpolants ?
  int          proof_reduce;                 // Enable proof reduction
  int		   proof_rec_piv;				 // Enable the use of RecyclePivots for reduction
  int		   proof_push_units;			// Enable pushing down units heuristics
  int          proof_struct_hash_build;		 // Enable structural hashing while building the proof
  int 		   proof_struct_hash;			 // Enable structural hashing for compression
  int 		   proof_switch_to_rp_hash;		 // Instead of hashing + rp does the opposite
  int 		   proof_transf_trav;			 // Enable transformation traversals
  int		   proof_check;					 // Enable proof checking
  double       proof_ratio_red_solv;         // Ratio reduction time solving time for each global loop
  double       proof_red_time;               // Reduction time for each global loop
  int	       proof_num_graph_traversals;   // Number of graph traversals in each global loop
  int          proof_red_trans;              // Number of reduction transformations loops
  int	       proof_random_context_analysis;// Examine a context with 50% probability
  int          proof_set_inter_algo;         // 0,1,2,3 to use McMillan,Pudlak,McMillan',minimal interpolant
  int		   proof_alternative_inter;		 // Dual formula for AB pivots
  int		   proof_multiple_inter;		 // Multiple interpolants
  int          proof_certify_inter;          // Check interpolants
  int          proof_interpolant_cnf;		 // Enable proof restructuring for interpolant in CNF
  int          proof_trans_strength;		 // Light proof restructuring for stronger/weaker interpolants, for Pudlak/McMillan/McMillan' algorithms


private:

  ofstream     stats_out;                    // File for statistics
  ofstream     out;                          // Regular output channel
  ofstream     err;                          // Diagnostic output channel
};
}
#endif
