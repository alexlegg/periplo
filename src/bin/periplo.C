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


#include "Egraph.h"
#include "PeriploContext.h"
#include "SimpSATSolver.h"
#include "Tseitin.h"
#include "TopLevelProp.h"

#include <cstdlib>
#include <cstdio>
#include <csignal>
#include <iostream>

#if defined(__linux__)
#include <fpu_control.h>
#endif

namespace periplo {

void        catcher            ( int );
extern bool stop;

} // namespace periplo

extern int  cnfset_in          ( FILE * );
extern int  cnfparse           ( );
extern int  smt2set_in         ( FILE * );
extern int  smt2parse          ( );
periplo::PeriploContext * parser_ctx;

/*****************************************************************************\
 *                                                                           *
 *                                  MAIN                                     *
 *                                                                           *
\*****************************************************************************/

int main( int argc, char * argv[] )
{
	periplo::stop = false;
	// Allocates Command Handler (since SMT-LIB 2.0)
	periplo::PeriploContext context( argc, argv );
	// Catch SigTerm, so that it answers even on ctrl-c
	signal( SIGTERM, periplo::catcher );
	signal( SIGINT , periplo::catcher );
	// Initialize pointer to context for parsing
	parser_ctx    = &context;
	const char * filename = argv[ argc - 1 ];
	assert( filename );
	// Accepts file from stdin if nothing specified
	FILE * fin = NULL;
	// Print help if required
	if ( strcmp( filename, "--help" ) == 0 || strcmp( filename, "-h" ) == 0 )
	{
		context.getConfig( ).printHelp( );
		return 0;
	}
	// File must be last arg
	if ( strncmp( filename, "--", 2 ) == 0 || strncmp( filename, "-", 1 ) == 0 )
		periplo_error( "input file must be last argument" );
	// Make sure file exists
	if ( argc == 1 )
		fin = stdin;
	else if ( (fin = fopen( filename, "rt" )) == NULL )
		periplo_error( "can't open file" );

	// Parse
	// Parse according to filetype
	if ( fin == stdin )
	{
		smt2set_in( fin );
		smt2parse( );
	}
	else
	{
		const char * extension = strrchr( filename, '.' );
/*
 	 	// NOTE DIMACS notation is not useful either for proof logging or
 	 	// interpolant generation
	    if ( strcmp( extension, ".cnf" ) == 0 )
		{
			context.SetLogic( QF_BOOL );
			cnfset_in( fin );
			cnfparse( );
			context.addCheckSAT();
		}
		else */
		if ( strcmp( extension, ".smt2" ) == 0 )
		{
			smt2set_in( fin );
			smt2parse( );
		}
		else
		{
			periplo_error2( extension, " extension not recognized. Please use .smt2 or stdin (SMT-LIB2 is assumed)" );
		}
	}

	fclose( fin );

	if ( context.getConfig( ).verbosity > 0 )
	{
		const int len_pack = strlen( PACKAGE_STRING );
		const char * site = "http://verify.inf.usi.ch/periplo";
		const int len_site = strlen( site );

		cerr << "#" << endl
				<< "# -------------------------------------------------------------------------" << endl
				<< "# " << PACKAGE_STRING;

		for ( int i = 0 ; i < 73 - len_site - len_pack ; i ++ )
			cerr << " ";

		cerr << site << endl
				<< "# Compiled with gcc " << __VERSION__ << " on " << __DATE__ << endl
				<< "# -------------------------------------------------------------------------" << endl
				<< "#" << endl;
	}

	//
	// This trick (copied from Main.C of MiniSAT) is to allow
	// the repeatability of experiments that might be compromised
	// by the floating point unit approximations on doubles
	//
#if defined(__linux__)
	fpu_control_t oldcw, newcw;
	_FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
#endif

#ifndef OPTIMIZE
	periplo_warning( "this binary is compiled with optimizations disabled (slow)" );
#endif
	//
	// Execute accumulated commands
	// function defined in PeriploContext.C
	//
	return context.executeCommands( );
}

namespace periplo {

void catcher( int sig )
{
	switch (sig)
	{
	case SIGINT:
	case SIGTERM:
		if ( periplo::stop )
		{
			parser_ctx->PrintResult( l_Undef );
			exit( 1 );
		}
		periplo::stop = true;
		break;
	}
}

} // namespace periplo
