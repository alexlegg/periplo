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

#ifndef GLOBAL_H
#define GLOBAL_H

#include <gmpxx.h>
#include <cassert>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <list>
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <stdint.h>
#include <limits.h>

#define periplo_error_() 		  { cerr << "# Error (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; assert(false); exit( 1 ); }
#define periplo_error( S )        { cerr << "# Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; assert(false); exit( 1 ); }
#define periplo_error2( S, T )    { cerr << "# Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; assert(false); exit( 1 ); }
#define periplo_warning( S )      { cerr << "# Warning: " << S << endl; }
#define periplo_warning2( S, T )  { cerr << "# Warning: " << S << " " << T << endl; }
#define reportf(format, args...) ( fflush(stdout), fprintf(stderr, format, ## args), fflush(stderr) )

#if ( __WORDSIZE == 64 )
#define BUILD_64
#endif

using std::set;
using std::map;
using std::vector;
using std::string;
using std::pair;
using std::make_pair;
using std::list;
using std::cout;
using std::cerr;
using std::endl;
using std::ostream;
using std::stringstream;
using std::ofstream;
using std::ifstream;

namespace periplo {

#define Pair( T ) pair< T, T >

typedef int       enodeid_t;
typedef enodeid_t snodeid_t;
#ifdef BUILD_64
typedef long enodeid_pair_t;
inline enodeid_pair_t encode( enodeid_t car, enodeid_t cdr )
{
	enodeid_pair_t p = car;
	p = p<<(sizeof(enodeid_t)*8);
	enodeid_pair_t q = cdr;
	p |= q;
	return p;
}
#else
typedef Pair( enodeid_t ) enodeid_pair_t;
inline enodeid_pair_t encode( enodeid_t car, enodeid_t cdr ) { return make_pair( car, cdr ); }
#endif
typedef enodeid_pair_t snodeid_pair_t;

// Set the bit B to 1 and leaves the others to 0
#define SETBIT( B ) ( 1 << (B) )

typedef enum
{
	UNDEF         // Undefined logic
	, EMPTY         // Empty, for the template solver
	, QF_UF         // Uninterpreted Functions
	, QF_BV         // BitVectors
	, QF_RDL        // Real difference logics
	, QF_IDL        // Integer difference logics
	, QF_LRA        // Real linear arithmetic
	, QF_LIA        // Integer linear arithmetic
	, QF_UFRDL      // UF + RDL
	, QF_UFIDL      // UF + IDL
	, QF_UFLRA      // UF + LRA
	, QF_UFLIA      // UF + LIA
	, QF_UFBV       // UF + BV
	, QF_AUFBV      // Arrays + UF + BV
	, QF_AX	  // Arrays with extensionality
	, QF_AXDIFF	  // Arrays with extensionality and diff
	, QF_BOOL       // Purely SAT instances
} logic_t;

static inline double cpuTime(void)
{
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}

#if defined(__linux__)
static inline int memReadStat(int field)
{
	char name[256];
	pid_t pid = getpid();
	sprintf(name, "/proc/%d/statm", pid);
	FILE*   in = fopen(name, "rb");
	if (in == NULL) return 0;
	int value;
	for (; field >= 0; field--)
		int ret = fscanf(in, "%d", &value);
	fclose(in);
	return value;
}

static inline uint64_t memUsed() { return (uint64_t)memReadStat(0) * (uint64_t)getpagesize(); }

#elif defined(__FreeBSD__) || defined(__OSX__) || defined(__APPLE__)
static inline uint64_t memUsed()
{
	char name[256];
	FILE *pipe;
	char buf[1024];
	uint64_t value=0;
	pid_t pid = getpid();
	sprintf(name,"ps -o rss -p %d | grep -v RSS", pid);
	pipe = popen(name, "r");
	if (pipe)
	{
		fgets(buf, 1024, pipe);
		value = 1024 * strtoul(buf, NULL, 10);
		pclose(pipe);
	}
	return value;
}
#else // stub to support every platform
static inline uint64_t memUsed() {return 0; }
#endif

#define CNF_STR "CNF_%d_%d"

#ifdef PRODUCE_PROOF
// For interpolation. When only 2 partitions
// are considered, these shorthands simplify
// readability
typedef enum
{ 
	I_UNDEF = 0
	, I_A     = 1
	, I_B     = 2
	, I_AB    = I_A | I_B
} icolor_t;
// For interpolation. Type that has to
// be used to store multiple partitions for
// a term
typedef mpz_class ipartitions_t;
// Set-bit
inline void setbit( ipartitions_t & p, const unsigned b ) { mpz_setbit( p.get_mpz_t( ), b ); }
inline void clrbit( ipartitions_t & p, const unsigned b ) { mpz_clrbit( p.get_mpz_t( ), b ); }
inline int tstbit( const ipartitions_t & p, const unsigned b ) { return mpz_tstbit( p.get_mpz_t( ), b ); }
// Function: void mpz_and (mpz_t rop, mpz_t op1, mpz_t op2)
// Set rop to op1 bitwise-and op2.
inline void andbit( ipartitions_t & ipres, ipartitions_t & ip1, ipartitions_t & ip2)
{ mpz_and( ipres.get_mpz_t( ), ip1.get_mpz_t( ), ip2.get_mpz_t( ) ); }
// Function: void mpz_or (mpz_t rop, mpz_t op1, mpz_t op2)
// Set rop to op1 bitwise inclusive-or op2.
inline void orbit( ipartitions_t & ipres, ipartitions_t & ip1, ipartitions_t & ip2)
{ mpz_ior( ipres.get_mpz_t( ), ip1.get_mpz_t( ), ip2.get_mpz_t( ) ); }
// Or-bit
// And-bit
// Basic operations
inline bool isABmixed( const ipartitions_t & p ) { return p % 2 == 1; }
inline bool isAlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && (p & ~mask) != 0; }
inline bool isBlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && (p &  mask) != 0; }
inline bool isAstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isAlocal( p, mask ) && !isBlocal( p, mask ); }
inline bool isBstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isBlocal( p, mask ) && !isAlocal( p, mask ); }
inline bool isAB     ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isAlocal( p, mask ) &&  isBlocal( p, mask ); }
#endif

#ifdef PRODUCE_PROOF
// To specify the tree structure of a collection of partitions
// NOTE Partitions should be tagged with consecutive ids >=1
class InterpolationTree
{
public:
	InterpolationTree(int _partition_id):
		partition_id(_partition_id),
		parent(NULL)
{}

	void addChild (InterpolationTree* _tree){
		children.insert(_tree);
		(*_tree).setParent(this);
	}

	void setParent(InterpolationTree* _parent){
		parent = _parent;
	}

	int getPartitionId() { return partition_id; }
	set<InterpolationTree*>& getChildren() { return children; }
	InterpolationTree* getParent() {return parent; }

private:
	// NOTE if the tree has N nodes, the partition ids go from 1 to N
	int partition_id;                         // The integer corresponding to the partition id
	set<InterpolationTree*>  children;        // The children of the node in the tree
	InterpolationTree* parent;
};
#endif

} // namespace periplo

#endif
