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

#ifndef THANDLER_H
#define THANDLER_H

#include "SATConfig.h"
#include "Egraph.h"

namespace periplo {
class SimpSATSolver;
}

using periplo::minisat::Var;
using periplo::minisat::Lit;

namespace periplo {

class EnodeHandler
{
public:

  EnodeHandler ( Egraph &      e, SATConfig &   c, SimpSATSolver &   s, const periplo::minisat::Var vt , const periplo::minisat::Var vf )
    : egraph             ( e )
    , config             ( c )
    , solver             ( s )
    , var_True           ( vt )
    , var_False          ( vf )
  { 
    // Reserve room for true and false
    var_to_enode   .resize( 65536, NULL );
    enode_id_to_var.resize( 65536, var_Undef );
  }
  
  virtual ~EnodeHandler ( ) { }
                                                 
  Var     enodeToVar           ( Enode * );             // Converts enode into boolean variable. Create a new variable if needed
  Lit     enodeToLit           ( Enode * );             // Converts enode into boolean literal. Create a new variable if needed
  Lit     enodeToLit           ( Enode *, Var & );      // Converts enode into boolean literal. Create a new variable if needed
  Enode * varToEnode           ( Var );                 // Return the enode corresponding to a variable
  void    clearVar             ( Var );                 // Clear a Var in translation table (used in incremental solving)
                               
private:                                 

  // Returns a random float 0 <= x < 1. Seed must never be 0.
  static inline double drand(double& seed) 
  {
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647; 
  }

  // Returns a random integer 0 <= x < size. Seed must never be 0.
  static inline int irand(double& seed, int size) 
  {
    return (int)(drand(seed) * size); 
  }

  vector< Var >       enode_id_to_var;          // Conversion EnodeID --> Var
  vector< Enode * >   var_to_enode;             // Conversion Var --> EnodeID
                                               
  Egraph &            egraph;                   // Pointer to Egraph that works as core solver
  SATConfig &         config;                   // Reference to configuration
  SimpSATSolver &     solver;                   // Reference to SAT Solver
  const Var           var_True;                 // To specify constantly true atoms
  const Var           var_False;                // To specify constantly false atoms
};
}
#endif
