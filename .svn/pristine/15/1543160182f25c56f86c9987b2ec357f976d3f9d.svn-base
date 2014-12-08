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

#include "Enode.h"

using namespace periplo;

#ifdef PRODUCE_PROOF

#define COLORED_ENODES 0

#if COLORED_ENODES
// For interpolation, prints node with
// color depending on its partition.
// Shared nodes are marked green, only
// for two partitions and for numbers
#define COL_START( C ) \
		{ \
	uint64_t color = 0; \
	ipartitions_t mask = 0; \
	mask = ~mask; \
	if ( C ==    2 ) color = 31; \
	else if ( C ==    4 ) color = 34; \
	else if ( C ==    8 ) color = 35; \
	else if ( C ==   16 ) color = 36; \
	else if ( C ==   32 ) color = 37; \
	else if ( C ==   64 ) color = 33; \
	else if ( C ==  128 ) color = 41; \
	else if ( C ==  256 ) color = 42; \
	else if ( C ==  512 ) color = 43; \
	else if ( C == 1024 ) color = 44; \
	else if ( C  >    1 \
			|| C == mask ) color = 32; \
			os.flush( ); \
			os << "\033[1" << ";" << color << "m"; \
			os.flush( ); \
		} \

#define COL_END \
		{ \
			os.flush( ); \
			os << "\033[0m"; \
			os.flush( ); \
		}
#else
#define COL_START( C ) { }
#define COL_END { }
#endif

#endif

//
// Constructor for ENIL
//
Enode::Enode( )
: id         ( ENODE_ID_ENIL )
, properties ( 0 )
, car        ( NULL )
, cdr        ( NULL )
#ifdef PRODUCE_PROOF
, ipartitions( 0 )
#endif
{ 
	setEtype( ETYPE_LIST );
	// dynamic = this;
}
//
// Constructor for new Symbols
//
Enode::Enode( const enodeid_t      id_
		, const char *         name_
		, const etype_t        etype_
		, Snode *              arg_sort_
		, Snode *              ret_sort_
)
: id         ( id_ )
, properties ( 0 )
, car        ( NULL )
, cdr        ( NULL )
#ifdef PRODUCE_PROOF
, ipartitions( 0 )
#endif
{
	setEtype( etype_ );
	if ( arg_sort_ )
		setArity( arg_sort_->getArity( ) ); // Sort arity includes return value ...
	symb_data = new SymbData( name_, etype_, arg_sort_, ret_sort_ );
}
//
// Constructor for new Terms/Lists
//
Enode::Enode( const enodeid_t id_
		, Enode *         car_
		, Enode *         cdr_ )
: id         ( id_ )
, properties ( 0 )
, car        ( car_ )
, cdr        ( cdr_ )
#ifdef PRODUCE_PROOF
, ipartitions( 0 )
#endif
{
	assert( car );
	assert( cdr );
	assert( car->isTerm( ) || car->isSymb( ) );
	assert( cdr->isList( ) );
	//
	// If car is term, then this node is a list
	//
	if ( car->isTerm( ) )
	{
		setEtype( ETYPE_LIST );
		if ( cdr->getArity( ) == MAX_ARITY - 1 )
			setArity( cdr->getArity( ) );
		else
			setArity( cdr->getArity( ) + 1 );
	}
	//
	// Otherwise this node is a term
	//
	else
	{
		//
		// Set Etype
		//
		setEtype( ETYPE_TERM );
		//
		// Set Arity
		//
		setArity( cdr->getArity( ) );
	}

	assert( isTerm( ) || isList( ) );
}
//
// Constructor for new Definition
//
Enode::Enode( const enodeid_t	id_
		, Enode *		def_ )
: id         ( id_ )
, properties ( ETYPE_DEF )
, car        ( def_ )
#ifdef PRODUCE_PROOF
, ipartitions( 0 )
#endif
{ }

Enode::~Enode ( )
{
	if ( isSymb( ) )
		delete symb_data;
}


void Enode::print( ostream & os )
{
	Enode * p = NULL;

	if( isSymb( ) )
		os << getName( );
	else if ( isTerm( ) )
	{
#ifdef PRODUCE_PROOF
		COL_START( ipartitions );
#endif

		if ( !cdr->isEnil( ) )
			os << "(";

		car->print( os );

		p = cdr;
		while ( !p->isEnil( ) )
		{
			os << " ";
			p->car->print( os );
			p = p->cdr;
		}

#ifdef PRODUCE_PROOF
		// Restart, it may have been shut down
		// by the previous loop
		COL_END;
		COL_START( ipartitions );
#endif

		if ( !cdr->isEnil( ) )
			os << ")";

#ifdef PRODUCE_PROOF
		COL_END;
#endif
	}
	else if ( isList( ) )
	{
		if ( isEnil( ) )
			os << "-";
		else
		{
			os << "[";
			car->print( os );

			p = cdr;
			while ( !p->isEnil( ) )
			{
				os << ", ";
				p->car->print( os );
				p = p->cdr;
			}

			os << "]";
		}
	}
	else if ( isDef( ) )
	{
		os << ":= " << car;
	}
	else if ( isEnil( ) )
	{
		os << "-";
	}
	else
		periplo_error( "unknown case value" );
}

void Enode::printSig( ostream & os )
{
#ifdef BUILD_64
	enodeid_pair_t sig = getSig( );
	os << "(" << (sig>>sizeof(enodeid_t)*8) << ", " << (sig|0x00000000FFFFFFFF) << ")";
#else
	Pair( enodeid_t ) sig = getSig( );
	os << "(" << sig.first << ", " << sig.second << ")";
#endif
}

string Enode::stripName( string s )
{
	return s.substr( 0, s.find( ' ', 0 ) );
}
