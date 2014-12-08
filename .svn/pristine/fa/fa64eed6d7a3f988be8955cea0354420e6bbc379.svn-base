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

#ifndef SSTORE_H
#define SSTORE_H

#include "Snode.h"
#include "SATConfig.h"
#include "SplayTree.h"

namespace periplo {

class SStore
{
public:

	SStore( SATConfig & c )
	: snil   ( new Snode )
	, config ( c )
	{
		//
		// Initialize nil key for splay tree
		//
		Snode * nilKey = const_cast< Snode * >( snil );
		store.setNil( nilKey );
		id_to_snode.push_back( const_cast< Snode * >( snil ) );
		initializeStore( );
	}

	~SStore( )
	{
		//
		// Delete snodes
		//
		while ( !id_to_snode.empty( ) )
		{
			if ( id_to_snode.back( ) != NULL )
				delete id_to_snode.back( );
			id_to_snode.pop_back( );
		}
	}

	//
	// Predefined constants nil, true, false
	// TODO: turn etrue efalse into constants
	//
	const Snode * const snil;

	//===========================================================================
	// Public APIs for snode construction/destruction

	Snode *  newSymbol           ( const char *, const bool = false );                            // Creates a sort symbol
	Snode *  newPara             ( const char * );                            // Creates a sort symbol
	Snode *  cons                ( list< Snode * > & );                                           // Shortcut, but not efficient
	Snode *  cons                ( Snode *, Snode * );                                            // Create Lists/Terms
	Snode *  cons                ( Snode * e ) { return cons( e, const_cast< Snode * >(snil) ); } // Shortcut for singleton

	inline Snode * mkDot         ( Snode * l )
	{
		assert( l->isList( ) );
		Snode * s = cons( id_to_snode[ SNODE_ID_DOT ], l );
		return s;
	}

	inline Snode * mkBool        ( ) { return cons( id_to_snode[ SNODE_ID_BOOL ] ); }
	Snode * mkVar         ( const char * );
	Snode * mkPara        ( const char * );

	void dumpSortsToFile ( ostream & );

private:
	//
	// TODO: Defines the set of operations that can be performed and that should be undone
	//
	typedef enum {      // These constants are stored on undo_stack_oper when
		SYMB            // A new symbol is created
		, PARA            // A new parameter
	} oper_t;

	SATConfig & config; // Reference to config

	//
	// Related to term creation
	//
	void    initializeStore ( );                                     // Initializes the store
	void    insertSymbol    ( Snode * );                             // Inserts a symbol
	void    removeSymbol    ( Snode * );                             // Remove a symbol
	Snode * lookupSymbol    ( const char * name );                   // Retrieve a symbol
	Snode * insertStore     ( const snodeid_t, Snode *, Snode * );   // Insert node into the global store

	SplayTree< Snode *, Snode::idLessThan > store;                   // The actual store
	map< string, Snode * >                  name_to_symbol;          // From sort name to pointer to symbol
	vector< Snode * >                       id_to_snode;             // Table SNODE_ID --> SNODE
};
}
#endif
