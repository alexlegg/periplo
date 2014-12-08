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

//
// Periplo Template Library
//
#ifndef OTL_H
#define OTL_H

#include "Global.h"
#include "SolverTypes.h"
//#include <ext/hash_map>
#include <tr1/unordered_set>
#include <tr1/unordered_map>

/*
namespace __gnu_cxx
{
// Hash function for pairs of integer
template<>
class hash< Pair( int ) >
{
public:
	size_t operator( )( const Pair( int ) & p ) const
	{
		return p.first ^ p.second;
	}
};
// Hash function for pairs of integer
template<>
class hash< periplo::minisat::Clause * >
{
public:
	size_t operator( )( periplo::minisat::Clause * c ) const
	{
		return (size_t)c;
	}
};
}
*/

namespace std {
namespace tr1 {
// Hash function for pairs of integer
template<>
class hash< Pair( int ) >
{
public:
	size_t operator( )( const Pair( int ) & p ) const
	{
		return p.first ^ p.second;
	}
};
// Hash function for pairs of integer
template<>
class hash< periplo::minisat::Clause * >
{
public:
	size_t operator( )( periplo::minisat::Clause * c ) const
	{
		return (size_t)c;
	}
};
}
}


struct strEq { inline bool operator( )( const char * s1, const char * s2 ) const { assert( s1 && s2 ); return strcmp( s1, s2 ) == 0; } };

#endif
