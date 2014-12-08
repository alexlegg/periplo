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

#ifndef ENODE_TYPES_H
#define ENODE_TYPES_H

#include "SolverTypes.h"
#include "Global.h"
#include "Snode.h"

namespace periplo {

//
// IMPORTANT: CHANGE THESE VALUES ONLY IF YOU KNOW WHAT YOU ARE DOING !!!
// IMPORTANT: CHANGE THESE VALUES ONLY IF YOU KNOW WHAT YOU ARE DOING !!!
// IMPORTANT: CHANGE THESE VALUES ONLY IF YOU KNOW WHAT YOU ARE DOING !!!
//
// Predefined list of identifiers to allow
// fast term creation for common operators
// Except for extract, which is created
// on demand
//
#define ENODE_ID_UNDEF	          (-1)
#define ENODE_ID_ENIL	           (0)
#define ENODE_ID_TRUE              (1)
#define ENODE_ID_FALSE             (2)
#define ENODE_ID_NOT               (3)
#define ENODE_ID_IMPLIES           (4)
#define ENODE_ID_AND               (5)
#define ENODE_ID_OR                (6)
#define ENODE_ID_XOR               (7)
#define ENODE_ID_EQ	           	   (8)
//                                
// IMPORTANT:
// This must be equal to the last predefined ID
// it is used to check whether a function symbol
// is predefined or uninterpreted
//
#define ENODE_ID_LAST		  (8)

//
// Properties stored in integers
//  31       28 27 26                20 19       16 15                                            0
// |EE|EE|EE|EE|NN|AA|AA|AA|AA|AA|AA|AA|TT|TT|TT|TT|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|
//   
// |<- etype ->|<------ arity -------->|<- dtype ->|<------------------ width -------------------->|
//
// Enode types
enum etype_t 
{ 
	ETYPE_UNDEF   = 0x00000000 // 0000 0000 0000 0000 0000 0000 0000 0000
	, ETYPE_SYMB    = 0x10000000 // 0001 0000 0000 0000 0000 0000 0000 0000
	, ETYPE_LIST    = 0x30000000 // 0011 0000 0000 0000 0000 0000 0000 0000
	, ETYPE_TERM    = 0x40000000 // 0100 0000 0000 0000 0000 0000 0000 0000
	, ETYPE_DEF     = 0x50000000 // 0101 0000 0000 0000 0000 0000 0000 0000
};

#define ETYPE_MASK  0xF0000000 // 1111 0000 0000 0000 0000 0000 0000 0000
#define ARITY_N     0x08000000 // 0000 1000 0000 0000 0000 0000 0000 0000
#define ARITY_MASK  0x07F00000 // 0000 0111 1111 0000 0000 0000 0000 0000
#define DTYPE_MASK  0x000F0000 // 0000 0000 0000 1111 0000 0000 0000 0000
#define WIDTH_MASK  0x0000FFFF // 0000 0000 0000 0000 1111 1111 1111 1111
#define MAX_WIDTH   (WIDTH_MASK) 
#define ARITY_SHIFT 20
#define MAX_ARITY   (ARITY_MASK >> ARITY_SHIFT)

//
// Some compile-time checks
//
#if !(ETYPE_MASK + ARITY_N + ARITY_MASK + DTYPE_MASK + WIDTH_MASK == 0xFFFFFFFF)
#error "Some macros are overlapping ?"
#endif

#if !(ARITY_MASK >> ARITY_SHIFT == 0x07F)
#error "Wrong value for ARITY_SHIFT ?"
#endif

//
// Forward declaration
//
class Enode;
//
// Data for symbols and numbers
//
struct SymbData
{
	//
	// Constructor for Symbols
	//
	SymbData ( const char *         name_
			, const etype_t        etype_
			, Snode *              arg_sort_
			, Snode *              ret_sort_ )
	: name     ( NULL )
	, arg_sort ( arg_sort_ )
	, ret_sort ( ret_sort_ )
	{
		//
		// Variable
		//
		if ( etype_ == ETYPE_SYMB )
		{
			name = new char[ strlen( name_ ) + 1 ];
			strcpy( name, name_ );
		}
	}

	~SymbData ( )
	{
		assert( name );
		delete [] name;
	}

	char *             name;
	Snode *            arg_sort;
	Snode *            ret_sort;
};
}

#endif
