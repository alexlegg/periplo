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

#ifndef ENODE_H
#define ENODE_H

#include "Global.h"
#include "EnodeTypes.h"
#include "Otl.h"

namespace periplo {

class Enode
{
public:

	//
	// Constructor for Enil
	//
	Enode  ( );
	//
	// Constructor for symbols
	//
	Enode ( const enodeid_t       // id
			, const char *          // name/value
			, const etype_t         // enode type
			, Snode *               // Sort args
			, Snode *               // Sort ret value
	);
	//
	// Constructor for terms and lists
	//
	Enode ( const enodeid_t       // id
			, Enode *               // car
			, Enode *               // cdr
	);
	//
	// Constructor for defs
	//
	Enode ( const enodeid_t       // id
			, Enode *	        // def
	);
	//
	// Destructor
	//
	~Enode ( );
	//
	// Check if a node is Enil
	//
	inline bool isEnil            ( ) const { return id == ENODE_ID_ENIL; }
	inline bool isList            ( ) const { return (properties & ETYPE_MASK) == ETYPE_LIST; }
	inline bool isTerm            ( ) const { return (properties & ETYPE_MASK) == ETYPE_TERM; }
	inline bool isSymb            ( ) const { return (properties & ETYPE_MASK) == ETYPE_SYMB; }
	inline bool isDef             ( ) const { return (properties & ETYPE_MASK) == ETYPE_DEF; }

	inline void setEtype          ( const etype_t t )
	{
		assert( t == ETYPE_SYMB || t == ETYPE_LIST || t == ETYPE_TERM || t == ETYPE_DEF );
		properties |= t;
	}

	inline void setArity            ( const unsigned a ) { assert( a <= ARITY_N ); properties |= (a << ARITY_SHIFT); }
	//
	// Check if a term node represents a certain symbol
	//
	inline bool isImplies           ( ) const { return hasSymbolId( ENODE_ID_IMPLIES     ); }
	inline bool isAnd               ( ) const { return hasSymbolId( ENODE_ID_AND         ); }
	inline bool isOr                ( ) const { return hasSymbolId( ENODE_ID_OR          ); }
	inline bool isNot               ( ) const { return hasSymbolId( ENODE_ID_NOT         ); }
	inline bool isXor               ( ) const { return hasSymbolId( ENODE_ID_XOR         ); }
	inline bool isIff               ( ) const { return hasSymbolId( ENODE_ID_EQ ) && get1st( )->hasSortBool( ); }
	inline bool isTrue              ( ) const { return hasSymbolId( ENODE_ID_TRUE        ); }
	inline bool isFalse             ( ) const { return hasSymbolId( ENODE_ID_FALSE       ); }

	inline bool isUp                ( ) const { return car->id > ENODE_ID_LAST && isAtom( ) && getArity( ) > 0; }
	inline bool isUf                ( ) const { return car->id > ENODE_ID_LAST && !isAtom( ) && getArity( ) > 0; }

	bool        isVar               ( ) const; // True if it is a variable
	bool        isConstant          ( ) const; // True if it is a constant
	bool        isLit               ( ) const; // True if it is a literal
	bool        isAtom              ( ) const; // True if it is an atom
	bool        isBooleanOperator   ( ) const; // True if it is a boolean operator

	inline bool hasSortBool( ) const
	{
		assert( isTerm( ) );
		return car->symb_data->ret_sort->hasSortBool( );
	}
	inline bool hasSortUndef( ) const
	{
		assert( isTerm( ) );
		return car->symb_data->ret_sort->hasSortUndef( );
	}

	//
	// Getty and Setty methods
	//
	inline enodeid_t            getId      ( ) const { return id; }
	inline unsigned             getArity   ( ) const { return ((properties & ARITY_MASK) >> ARITY_SHIFT); }
	Snode *                     getArgSort ( ) const { assert( isTerm( ) || isSymb( ) ); return isTerm( ) ? car->symb_data->arg_sort : symb_data->arg_sort; }
	Snode *                     getRetSort ( ) const { assert( isTerm( ) || isSymb( ) ); return isTerm( ) ? car->symb_data->ret_sort : symb_data->ret_sort; }
	inline string   getName                ( )       { assert( isSymb( ) ); assert( symb_data ); return stripName( symb_data->name ); }
	inline string   getNameFull            ( )       { assert( isSymb( ) ); assert( symb_data ); return symb_data->name; }
	inline const char*   getNameFullC      ( )       { assert( isSymb( ) ); assert( symb_data ); return symb_data->name; }
	inline Enode *  getCar                 ( ) const { return car; }
	inline Enode *  getCdr                 ( ) const { return cdr; }
	inline Enode *  getDef                 ( ) const { assert( isDef( ) ); assert( car ); return car; }

	Enode *         getRoot                ( ) const { assert( !isDef( ) ); return const_cast<Enode *>(this); }
	enodeid_t       getCid                 ( ) const {	assert( !isDef( ) ); return id; }

	inline int      getWidth               ( ) const { assert( isTerm( ) || isSymb( ) ); return (properties & WIDTH_MASK); }
	inline void     setWidth               ( const uint32_t w )
	{
		assert( isTerm( ) );
		assert( w < MAX_WIDTH );
		// Reset width
		properties &= ~WIDTH_MASK;
		properties |= w;
		assert( getWidth( ) == static_cast<int>( w ) );
	}

	inline void    setDef                 ( Enode * e )        { assert( e ); assert( isDef( ) ); car = e; }

	//
	// Shortcuts for retrieving a term's arguments
	//
	inline Enode * get1st                 ( ) const;     // Get first argument in constant time
	inline Enode * get2nd                 ( ) const;     // Get second argument in constant time
	inline Enode * get3rd                 ( ) const;     // Get third argument in constant time

	unsigned       sizeInMem              ( ) const;

	void           print	                ( ostream & ); // Prints the enode
	string         stripName              ( string );
	void           printSig	        ( ostream & ); // Prints the enode signature

#ifdef BUILD_64
	inline enodeid_pair_t          getSig    ( ) const { return encode( car->getRoot( )->getCid( ), cdr->getRoot( )->getCid( ) ); }
#else
	inline const Pair( enodeid_t ) getSig    ( ) const { return make_pair( car->getRoot( )->getCid( ), cdr->getRoot( )->getCid( ) ); }
#endif
	inline enodeid_t               getSigCar ( ) const { return car->getRoot( )->getCid( ); }
	inline enodeid_t               getSigCdr ( ) const { return cdr->getRoot( )->getCid( ); }

#ifdef PRODUCE_PROOF
	inline const ipartitions_t & getIPartitions ( ) const                   { return ipartitions; }
	inline void                  setIPartitions ( const ipartitions_t & p ) { assert( ipartitions == 0 ); ipartitions = p; }
	inline void                  addIPartitions ( const ipartitions_t & p ) { assert( p != 0 ); ipartitions |= p; }
	// inline void                  oveIPartitions ( const ipartitions_t & p ) { assert( p != 0 ); ipartitions = p; }
#endif

	inline friend ostream & operator<<( ostream & os, Enode * e )    { assert( e ); e->print( os ); return os; }

	struct idLessThan
	{
		inline bool operator( )( Enode * x, Enode * y ) const
		{
			const Enode *x_car = x->getCar();
			const Enode *y_car = y->getCar();
			const enodeid_t x_car_id = x_car->getId();
			const enodeid_t y_car_id = y_car->getId();

			return (x_car_id < y_car_id)
					|| (x_car_id == y_car_id && x->getCdr( )->getId( ) < y->getCdr( )->getId( ) );
		}
	};

	struct cidLessThan
	{
		inline bool operator( )( Enode * x, Enode * y ) const
		{
			if ( x == y ) return false;
			if ( x->isEnil( ) ) return true;
			if ( y->isEnil( ) ) return false;
			return (x->getCar( )->getCid( ) <  y->getCar( )->getCid( ))
					|| (x->getCar( )->getCid( ) == y->getCar( )->getCid( ) && x->getCdr( )->getCid( ) < y->getCdr( )->getCid( ) );
		}
	};

private:
	//
	// Standard informations for terms
	//
	const enodeid_t   id;          // Node unique identifier
	uint32_t          properties;  // Contains all the properties of this node (see EnodeTypes.h for bitfields definition)
	Enode *           car;         // For car / defs
	Enode *           cdr;         // For cdr
	SymbData *        symb_data;   // For symbols/numbers
#ifdef PRODUCE_PROOF
	ipartitions_t     ipartitions; // Partitions for interpolation
#endif

	inline bool       hasSymbolId    ( const enodeid_t id ) const { assert( isTerm( ) ); return car->getId( ) == id; }
};
}

//
// enode is a literal if it is
// an atom or a negated atom
//
inline bool periplo::Enode::isLit( ) const
{
	if ( !isTerm( ) ) return false;
	if ( isAtom( ) ) return true;
	// if ( car->getArity( ) != ENODE_ARITY_1 ) return false;
	if ( getArity( ) != 1 ) return false;
	Enode * arg = get1st( );
	return isNot( ) && arg->isAtom( );
}
//
// enode is an atom if it has boolean type and
// it is not a boolean operator. Constants true
// and false are considered atoms
//
inline bool periplo::Enode::isAtom( ) const
{
	if ( !isTerm( ) ) return false;
	if ( !hasSortBool( ) ) return false;
	if ( isBooleanOperator( ) ) return false;

	return true;
}

inline bool periplo::Enode::isVar( ) const
{
	if ( car->getId( )    <= ENODE_ID_LAST ) return false;     // If the code is predefined, is not a variable
	if ( isConstant( ) ) return false;                         // If it's a constant is not a variable
	if ( !isTerm( ) ) return false;		             // If is not a term is not a variable
	if ( getArity( ) != 0 ) return false;
	return car->isSymb( );	                             // Final check
}

inline bool periplo::Enode::isConstant( ) const
{
	if ( !isTerm( ) ) return false;		         // Check is a term
	return isTrue( ) || isFalse( );      // Only true, false are constant
}

inline bool periplo::Enode::isBooleanOperator( ) const
{
	return isAnd( ) || isOr( )  || isNot( ) || isIff( ) || isXor( ) || isImplies( );
}

inline periplo::Enode * periplo::Enode::get1st ( ) const
{
	assert( isTerm( ) );
	assert( getArity( ) > 0 );
	return getCdr( )->getCar( );
}

inline periplo::Enode * periplo::Enode::get2nd ( ) const
{
	assert( isTerm( ) );
	assert( getArity( ) > 1 );
	return getCdr( )->getCdr( )->getCar( );
}

inline periplo::Enode * periplo::Enode::get3rd ( ) const
{
	assert( isTerm( ) );
	assert( getArity( ) > 2 );
	return getCdr( )->getCdr( )->getCdr( )->getCar( );
}

inline unsigned periplo::Enode::sizeInMem( ) const
{
	unsigned size = sizeof( Enode );
	if ( isSymb( ) )
	{
		assert( symb_data );
		assert( symb_data->name );
		size += sizeof( SymbData ) + strlen( symb_data->name );
	}
#ifdef PRODUCE_PROOF
	size += ipartitions.get_mpz_t()->_mp_alloc * sizeof(ipartitions.get_mpz_t()->_mp_d[0]);
#endif
	return size;
}


#endif
