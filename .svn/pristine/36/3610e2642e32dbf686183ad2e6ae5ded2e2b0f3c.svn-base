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

#ifndef TOP_LEVEL_PROP_H
#define TOP_LEVEL_PROP_H

#include "Global.h"
#include "Otl.h"
#include "Egraph.h"

namespace periplo {

class TopLevelProp
{
public:

  TopLevelProp ( Egraph & egraph_, SATConfig & config_ )
    : egraph  ( egraph_ )
    , config  ( config_ )
  { }

  virtual ~TopLevelProp( ) { }

  Enode * doit ( Enode * ); // Main routine

private:

  bool    retrieveSubstitutions           ( Enode *
                                          , map< Enode *, Enode * > & 
                                          , map< Enode *, Enode * > & );
  bool    contains                        ( Enode *, Enode * );
  Enode * substitute                      ( Enode *, map< Enode *, Enode * > &, bool & );
  void    computeIncomingEdges            ( Enode *, vector< int > & );
  
  Egraph &    egraph; // Reference to Egraph
  SATConfig & config; // Reference to Config
};
}

#endif
