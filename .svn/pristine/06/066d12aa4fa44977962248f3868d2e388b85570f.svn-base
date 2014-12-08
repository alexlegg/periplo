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

#include "SATConfig.h"

using namespace periplo;
using namespace periplo::minisat;

void SATConfig::initializeConfig( )
{
	// Set Global Default configuration
	logic                         = UNDEF;
	status                        = l_Undef;
	incremental                   = 0;
	produce_stats                 = 0;
	produce_models                = 0;
	print_stats                   = 0;
	dump_formula                  = 0;
	verbosity                     = 0;
	print_success                 = false;
	certification_level           = 0;
	strcpy( certifying_solver, "./tool_wrapper.sh" );
	// Set SAT-Solver Default configuration
	sat_restart_first             = 100;
	sat_restart_inc               = 1.1;
	sat_use_luby_restart          = 0;
	sat_learn_up_to_size          = 0;
	sat_temporary_learn           = 1;
	sat_preprocess_booleans       = 1;
	sat_centrality                = 18;
	sat_trade_off                 = 8192;
	sat_minimize_conflicts        = 1;
	sat_dump_cnf                  = 0;
	sat_dump_rnd_inter            = 0;
	sat_propagate_small			  = 0;
	// Proof parameters
	print_proofs_smtlib2          = 0;
	print_proofs_dotty	        = 0;
	produce_inter                 = 0;
	proof_reduce                  = 0;
	proof_rec_piv                  = 1;
	proof_transf_trav			 = 1;
	proof_struct_hash			= 1;
	proof_struct_hash_build      = 0;
	proof_switch_to_rp_hash		 = 0;
	proof_push_units			 = 1;
	proof_check					  = 0;
	proof_ratio_red_solv          = 0;
	proof_red_time                = 0;
	proof_num_graph_traversals    = 0;
	proof_red_trans               = 0;
	proof_random_context_analysis = 0;
	proof_set_inter_algo          = 0;
	proof_alternative_inter		= 0;
	proof_multiple_inter		= 0;
	proof_certify_inter           = 0;
	proof_interpolant_cnf         = 0;
	proof_trans_strength		 = 0;
	sat_restart_learnt_thresh	 = 0;
	sat_orig_thresh				 = 0;
}

void SATConfig::parseConfig ( char * f )
{
	FILE * filein = NULL;
	// Open configuration file
	if ( ( filein = fopen( f, "rt" ) ) == NULL )
	{
		// No configuration file is found. Print out
		// the current configuration
		// cerr << "# " << endl;
		cerr << "# WARNING: No configuration file " << f << ". Dumping default setting to " << f << endl;
		ofstream fileout( f );
		printConfig( fileout );
		fileout.close( );
	}
	else
	{
		int line = 0;

		while ( !feof( filein ) )
		{
			line ++;
			char buf[ 128 ];
			char * res = fgets( buf, 128, filein );
			(void)res;
			// Stop if finished
			if ( feof( filein ) )
				break;
			// Skip comments
			if ( buf[ 0 ] == '#' )
				continue;

			char tmpbuf[ 32 ];

			// GENERIC CONFIGURATION
			if ( sscanf( buf, "incremental %d\n"             , &incremental )                   == 1 );
			else if ( sscanf( buf, "produce_stats %d\n"           , &produce_stats )                 == 1 );
			else if ( sscanf( buf, "print_stats %d\n"             , &print_stats )                   == 1 );
			else if ( sscanf( buf, "produce_models %d\n"          , &produce_models )                == 1 );
			else if ( sscanf( buf, "regular_output_channel %s\n"   , tmpbuf )                         == 1 )
				setRegularOutputChannel( tmpbuf );
			else if ( sscanf( buf, "diagnostic_output_channel %s\n", tmpbuf )                         == 1 )
				setDiagnosticOutputChannel( tmpbuf );
			else if ( sscanf( buf, "dump_formula %d\n"             , &dump_formula )                  == 1 );
			else if ( sscanf( buf, "verbosity %d\n"                , &verbosity )                     == 1 );
			else if ( sscanf( buf, "certification_level %d\n"      , &certification_level )           == 1 );
			else if ( sscanf( buf, "certifying_solver %s\n"        , certifying_solver )              == 1 );
			// SAT SOLVER CONFIGURATION
			else if ( sscanf( buf, "sat_restart_first %d\n"        , &(sat_restart_first))            == 1 );
			else if ( sscanf( buf, "sat_restart_increment %lf\n"   , &(sat_restart_inc))              == 1 );
			else if ( sscanf( buf, "sat_use_luby_restart %d\n"     , &(sat_use_luby_restart))         == 1 );
			else if ( sscanf( buf, "sat_learn_up_to_size %d\n"     , &(sat_learn_up_to_size))         == 1 );
			else if ( sscanf( buf, "sat_temporary_learn %d\n"      , &(sat_temporary_learn))          == 1 );
			else if ( sscanf( buf, "sat_preprocess_booleans %d\n"  , &(sat_preprocess_booleans))      == 1 );
			else if ( sscanf( buf, "sat_centrality %d\n"           , &(sat_centrality))               == 1 );
			else if ( sscanf( buf, "sat_trade_off %d\n"            , &(sat_trade_off))                == 1 );
			else if ( sscanf( buf, "sat_minimize_conflicts %d\n"   , &(sat_minimize_conflicts))       == 1 );
			else if ( sscanf( buf, "sat_dump_cnf %d\n"             , &(sat_dump_cnf))                 == 1 );
			else if ( sscanf( buf, "sat_propagate_small %d\n"      , &(sat_propagate_small))          == 1 );
			else if ( sscanf( buf, "sat_restart_learnt_thresh %d\n", &(sat_restart_learnt_thresh))    == 1 );
			else if ( sscanf( buf, "sat_orig_thresh %d\n"		   , &(sat_orig_thresh))    		  == 1 );
			// PROOF PRODUCTION CONFIGURATION
			else if ( sscanf( buf, "print_proofs_smtlib2 %d\n"    , &print_proofs_smtlib2 )          == 1 );
			else if ( sscanf( buf, "print_proofs_dotty %d\n"      , &print_proofs_dotty )            == 1 );
			else if ( sscanf( buf, "sat_dump_rnd_inter %d\n"       , &(sat_dump_rnd_inter))           == 1 );
			else if ( sscanf( buf, "proof_reduce %d\n"             , &(proof_reduce))                 == 1 );
			else if ( sscanf( buf, "proof_rec_piv %d\n"             , &(proof_rec_piv))                 == 1 );
			else if ( sscanf( buf, "proof_push_units %d\n"          , &(proof_push_units))                 == 1 );
			else if ( sscanf( buf, "proof_struct_hash %d\n"         , &(proof_struct_hash))                 == 1 );
			else if ( sscanf( buf, "proof_struct_hash_build %d\n"   , &(proof_struct_hash_build))                 == 1 );
			else if ( sscanf( buf, "proof_switch_to_rp_hash %d\n"   , &(proof_switch_to_rp_hash))                 == 1 );
			else if ( sscanf( buf, "proof_transf_trav %d\n"         , &(proof_transf_trav))                 == 1 );
			else if ( sscanf( buf, "proof_check %d\n"             , &(proof_check))                 == 1 );
			else if ( sscanf( buf, "proof_ratio_red_solv %lf\n"    , &(proof_ratio_red_solv))         == 1 );
			else if ( sscanf( buf, "proof_red_time %lf\n"          , &(proof_red_time))               == 1 );
			else if ( sscanf( buf, "proof_num_graph_traversals %d\n" , &(proof_num_graph_traversals)) == 1 );
			else if ( sscanf( buf, "proof_red_trans %d\n"          , &(proof_red_trans))              == 1 );
			else if ( sscanf( buf, "proof_random_context_analysis %d\n"     , &(proof_random_context_analysis)) == 1 );
			else if ( sscanf( buf, "proof_set_inter_algo %d\n"     , &(proof_set_inter_algo))         == 1 );
			else if ( sscanf( buf, "proof_alternative_inter %d\n"     , &(proof_alternative_inter))         == 1 );
			else if ( sscanf( buf, "proof_multiple_inter %d\n"     , &(proof_multiple_inter))         == 1 );
			else if ( sscanf( buf, "proof_interpolant_cnf %d\n"     , &(proof_interpolant_cnf))         == 1 );
			else if ( sscanf( buf, "proof_trans_strength %d\n"     , &(proof_trans_strength))         == 1 );
			else if ( sscanf( buf, "proof_certify_inter %d\n"      , &(proof_certify_inter))          == 1 );
			else
			{
				periplo_error2( "unrecognized option ", buf );
			}
		}

		// Close
		fclose( filein );
	}

	if ( produce_stats ) stats_out.open( "stats.out" );
}

void SATConfig::printConfig ( ostream & out )
{
	out << "#" << endl;
	out << "# PeRIPLO Configuration File" << endl;
	out << "# . Options may be written in any order" << endl;
	out << "# . Unrecognized options will throw an error" << endl;
	out << "# . Use '#' for line comments" << endl;
	out << "# . Remove this file and execute PeRIPLO to generate a new copy with default values" << endl;
	out << "#" << endl;
	out << "# GENERIC CONFIGURATION" << endl;
	out << "#" << endl;
	//out << "# Enables incrementality (SMT-LIB 2.0 script-compatible)" << endl;
	//out << "incremental "                << incremental << endl;
	out << "# Regular output channel " << endl;
	out << "regular_output_channel stdout" << endl;
	out << "# Diagnostic output channel " << endl;
	out << "diagnostic_output_channel stderr" << endl;
	out << "# Prints statistics in stats.out" << endl;
	out << "produce_stats "              << produce_stats << endl;
	out << "# Prints statistics to screen" << endl;
	out << "print_stats "              << print_stats << endl;
	out << "# Prints models" << endl;
	out << "produce_models "             << produce_models << endl;
	out << "# Dumps input formula (debugging)" << endl;
	out << "dump_formula "               << dump_formula << endl;
	out << "# Choose verbosity level" << endl;
	out << "verbosity "                  << verbosity << endl;
	out << "#" << endl;
	out << "# SAT SOLVER CONFIGURATION" << endl;
	out << "#" << endl;
	//out << "# Initial and increment conflict limits for restart" << endl;
	//out << "sat_restart_first "       << sat_restart_first << endl;
	//out << "sat_restart_increment "   << sat_restart_inc << endl;
	//out << "sat_use_luby_restart "    << sat_use_luby_restart << endl;
	//out << "# Learn clauses up to the specified size (0 learns nothing)" << endl;
	//out << "sat_learn_up_to_size "    << sat_learn_up_to_size << endl;
	//out << "sat_temporary_learn "     << sat_temporary_learn << endl;
	out << "# Preprocess variables and clauses when possible" << endl;
	out << "sat_preprocess_booleans " << sat_preprocess_booleans << endl;
	//out << "sat_centrality "          << sat_centrality << endl;
	//out << "sat_trade_off "           << sat_trade_off << endl;
	//out << "sat_minimize_conflicts "  << sat_minimize_conflicts << endl;
	out << "sat_dump_cnf "            << sat_dump_cnf << endl;
	out << "# Try to propagate first smaller clauses " << endl;
	out << "sat_propagate_small " << sat_propagate_small << endl;
	out << "# Restart solver if current learnt width is greater than threshold (>0)" << endl;
	out << "sat_restart_learnt_thresh " << sat_restart_learnt_thresh << endl;
	out << "# Uses only original clauses of width up to threshold (>0)" << endl;
	out << "sat_orig_thresh " << sat_orig_thresh << endl;
	out << "#" << endl;
	out << "# PROOF TRANSFORMER AND INTERPOLATOR CONFIGURATION" << endl;
	out << "# Remember to add in the SMTLIB2 file " << endl;
	out	<< "# (get-proof) or (set-option :produce-interpolants true) plus (get-interpolants)" << endl;
	out << "# " << endl;
	out << "# Prints proofs"  << endl;
	out << "print_proofs_smtlib2 "       << print_proofs_smtlib2 << endl;
	out << "print_proofs_dotty "         << print_proofs_dotty << endl;
	out << "# Enable proof checking" << endl;
	out << "proof_check "             << proof_check << endl;
	out << "# Generate a new SMTLIB2 file by splitting the input formula into (sat_dump_rnd_inter+1) partitions" << endl;
	out << "sat_dump_rnd_inter "      << sat_dump_rnd_inter << endl;
	out << "# Set to 0,1,2,3 to use McMillan, Pudlak, McMillan', minimal interpolation algorithm" << endl;
	out << "proof_set_inter_algo "      << proof_set_inter_algo << endl;
	out << "# Use dual formula for interpolant minimization in Pudlak" << endl;
	out << "proof_alternative_inter "      << proof_alternative_inter << endl;
	out << "# Choose: "<< endl;
	out << "# 0 for path interpolation, 1 for simultaneous abstraction" << endl;
	out << "# 2 for gen. simultaneous abstraction, 3 for state-transition interpolation" << endl;
	out << "proof_multiple_inter "      << proof_multiple_inter << endl;
	out << "# Enable proof restructuring step for generation of interpolants (partially) in CNF" << endl;
	out << "# Needs exactly two partitions and McMillan interpolation algorithm" << endl;
	out << "proof_interpolant_cnf " << proof_interpolant_cnf << endl;
	out << "# Enable light proof restructuring step for generation of stronger/weaker interpolants" << endl;
	out << "# Needs exactly two partitions and McMillan/McMillan'/Pudlak interpolation algorithm" << endl;
	out << "# 1 for stronger interpolants, 2 for weaker interpolants" << endl;
	out << "proof_trans_strength " << proof_trans_strength << endl;
	out << "# Enable certification of interpolants" << endl;
	out << "proof_certify_inter "      << proof_certify_inter << endl;
	out << "certifying_solver " << certifying_solver << endl;
	out << "# Proof reduction is based on a run of LowerUnits followed by a number of global iterations." << endl;
	out << "# Each global iteration consists of: RecyclePivots, StructuralHashing, TransformationTraversals" << endl;
	out << "# Enable structural hashing while building proof" << endl;
	out << "proof_struct_hash_build " << proof_struct_hash_build << endl;
	out << "# Enable proof reduction" << endl;
	out << "proof_reduce "             << proof_reduce << endl;
	out << "# Enable LowerUnits" << endl;
	out << "proof_push_units " << proof_push_units << endl;
	out << "# Enable RecyclePivots" << endl;
	out << "proof_rec_piv "             << proof_rec_piv << endl;
	out << "# Enable StructuralHashing" << endl;
	out << "proof_struct_hash " << proof_struct_hash << endl;
	out << "# Invert the normal order StructuralHashing -> RecyclePivots" << endl;
	out << "proof_switch_to_rp_hash " << 	proof_switch_to_rp_hash << endl;
	out << "# Enable proof TransformationTraversals" << endl;
	out << "proof_transf_trav " << proof_transf_trav << endl;
	out << "# Reduction timeout w.r.t. solving time for each global iteration" << endl;
	out << "proof_ratio_red_solv "     << proof_ratio_red_solv << endl;
	out << "# Reduction timeout for each global iteration" << endl;
	out << "proof_red_time "           << proof_red_time << endl;
	out << "# Number of TransformationTraversals for each global iteration" << endl;
	out << "proof_num_graph_traversals "   << proof_num_graph_traversals << endl;
	out << "# Number of global iterations" << endl;
	out << "proof_red_trans "          << proof_red_trans << endl;
	//out << "# Randomize examination of rule contexts" << endl;
	//out << "proof_random_context_analysis " << proof_random_context_analysis << endl;
	out << "#" << endl;
	out << "#" << endl;
}

void SATConfig::parseCMDLine( int argc
		, char * argv[ ] )
{
	char config_name[ 64 ];
	for ( int i = 1 ; i < argc - 1 ; i ++ )
	{
		const char * buf = argv[ i ];
		// Parsing of configuration options
		if ( sscanf( buf, "--config=%s", config_name ) == 1 )
		{
			parseConfig( config_name );
			break;
		}
		else if ( strcmp( buf, "--help" ) == 0
				|| strcmp( buf, "-h" ) == 0 )
		{
			printHelp( );
			exit( 1 );
		}
		else
		{
			printHelp( );
			periplo_error2( "unrecognized option", buf );
		}
	}
}

void SATConfig::printHelp( )
{
	const char help_string[]
	                       = "Usage: ./periplo [OPTION] filename\n"
	                    		   "where OPTION can be\n"
	                    		   "  --help [-h]              print this help\n"
	                    		   "  --config=<filename>      use configuration file <filename>\n";
	cerr << help_string;
}
