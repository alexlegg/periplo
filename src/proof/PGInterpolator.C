/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

Periplo -- Copyright (C) 2013, Simone Fulvio Rollini

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

#ifdef PRODUCE_PROOF
#include "PG.h"

using namespace periplo;

// Path interpolation
// Partitions   phi_1 ... phi_n
// Interpolants I_0 ... I_n
// Generation I_i = Itp(phi_1 ... phi_i | phi_{i+1} ... phi_n)
// Requirement  I_i /\ phi_{i+1} -> I_{i+1}
bool ProofGraph::producePathInterpolants( vector< Enode * > & interpolants )
{
	assert( interpolants.size( ) == 0 );
	unsigned nparts = egraph.getNofPartitions();
	if(nparts==2) { produceSingleInterpolant(interpolants); return true;  }

	if( verbose() ) cerr << "# Path interpolation " << endl;

	// Generate appropriate masks
	vector< ipartitions_t > configs;
	configs.resize(egraph.getNofPartitions() + 1,0);
	// First interpolant is true -> all partitions in B
	for( unsigned i = 1; i < configs.size(); i++ )
	{
		configs[i] = configs[i-1];
		// Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
		setbit(configs[i],i);
	}

	produceMultipleInterpolants( configs, interpolants );
	bool property_holds = true;
	if( enabledInterpVerif() ) property_holds = verifyPathInterpolantsFromLeaves( interpolants );
	return property_holds;
}

// Simultaneous abstraction
// Partitions   phi_1 ... phi_n
// Interpolants I_1 ... I_n
// Generation 	I_i = Itp(phi_i | phi_1 ... phi_{i-1}, phi_{i+1} ... phi_n)
// Requirement  I_i /\ ... /\ I_n -> false
bool ProofGraph::produceSimultaneousAbstraction( vector< Enode * > & interpolants )
{
	assert( interpolants.size( ) == 0 );
	unsigned nparts = egraph.getNofPartitions();
	if(nparts==2) { produceSingleInterpolant(interpolants); return true;  }

	if( verbose() ) cerr << "# Simultaneous abstraction " << endl;

	// Generate appropriate masks
	vector< ipartitions_t > configs;
	configs.resize(egraph.getNofPartitions(),0);

	for( unsigned i = 0; i < configs.size(); i++ )
	{
		// Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
		setbit(configs[i],i+1);
	}
	produceMultipleInterpolants( configs, interpolants );
	bool property_holds = true;
	if( enabledInterpVerif() ) property_holds = verifySimultaneousAbstraction( interpolants );
	return property_holds;
}

// Generalized simultaneous abstraction
// Partitions   phi_1 ... phi_n
// Interpolants I_1 ... I_n
// Generation 	for 1<=i<=n-1     I_i = Itp(phi_i | phi_1 ... phi_{i-1}, phi_{i+1} ... phi_n)
//				for i=n			  I_n = Itp(phi_1 ... phi_{n-1} | phi_n)
// Requirement  I_i /\ ... /\ I_{n-1} -> I_n
bool ProofGraph::produceGenSimultaneousAbstraction( vector< Enode * > & interpolants )
{
	assert( interpolants.size( ) == 0 );
	unsigned nparts = egraph.getNofPartitions();
	if(nparts==2) { produceSingleInterpolant(interpolants); return true;  }

	if( verbose() ) cerr << "# Generalized simultaneous abstraction " << endl;

	// Generate appropriate masks
	vector< ipartitions_t > configs;
	configs.resize(nparts,0);

	for( unsigned i = 0; i < nparts-1; i++ )
	{
		// Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
		setbit(configs[i],i+1);
		// Update last configuration for I_n
		setbit(configs[nparts-1],i+1);
	}
	produceMultipleInterpolants( configs, interpolants );
	bool property_holds = true;
	if( enabledInterpVerif() ) property_holds = verifyGenSimultaneousAbstraction( interpolants );
	return property_holds;
}

// State transition interpolation
// Partitions   phi_1 ... phi_n
// Interpolants I_0 ... I_n, J_1 ... J_n
// Generation 	I_i = Itp(phi_1 ... phi_i | phi_{i+1} ... phi_n)
// 				J_i = Itp(phi_i | phi_1 ... phi_{i-1}, phi_{i+1} ... phi_n)
// Requirement  I_i /\ J_{i+1} -> I_{i+1}
bool ProofGraph::produceStateTransitionInterpolants( vector< Enode * > & interpolants )
{
	assert( interpolants.size( ) == 0 );
	unsigned npart = egraph.getNofPartitions();
	if(npart==2) { produceSingleInterpolant(interpolants); return true;  }

	if( verbose() ) cerr << "# State-transition interpolation " << endl;

	// Generate appropriate masks
	vector< ipartitions_t > configs;
	configs.resize((2*npart) + 1,0);

	// All the path interpolants
	// First interpolant is true -> all partitions in B
	for( unsigned i = 1; i < (npart + 1); i++ )
	{
		configs[i] = configs[i-1];
		// Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
		setbit(configs[i],i);
	}

	// All the symmetric interpolants
	for( unsigned i = (npart + 1); i < configs.size(); i++ )
	{
		// Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
		setbit(configs[i],(i-npart-1)+1);
	}
	produceMultipleInterpolants( configs, interpolants );

	bool property_holds = true;
	if( enabledInterpVerif() ) property_holds = verifyStateTransitionInterpolants( interpolants );
	return property_holds;
}

void ProofGraph::produceConfigMatrixInterpolants(const vector< vector<int> > &configs, vector<Enode*> &interpolants)
{
	if( verbose() ) cerr << "# General interpolation via configuration matrix " << endl;

	// Generate appropriate masks
	vector< ipartitions_t > parts;
	parts.resize(configs.size(),0);
	// First interpolant is true -> all partitions in B
	for( unsigned i = 0; i < parts.size(); i++ )
	{
		for (unsigned j = 0; j < configs[i].size(); ++j)
		{
			// Set partitions[i] bit to 1 (starting from bit 1, bit 0 is untouched)
			// NOTE remember that partition ids are numbered from 0 in FunFrog!
			setbit( parts[i], configs[i][j]+1 );
		}
	}
	produceMultipleInterpolants( parts, interpolants );
}

// Tree interpolation
// Partitions   phi_1 ... phi_n
// Subtrees		F_1   ... F_n
// Interpolants I_1 ... I_n
// Generation 	I_i = Itp(F_i | all other formulae)
// Requirement  ( /\_(i,j) I_j /\ phi_i ) -> I_i
bool ProofGraph::produceTreeInterpolants(periplo::InterpolationTree* it, vector<Enode*> &interpolants)
{
	if( verbose() ) cerr << "# Tree interpolation " << endl;

	// NOTE some configurations might be empty,
	// if the corresponding nodes in the tree are not approximated
	// TODO

	// Generate appropriate masks
	// NOTE partition ids start from 1, parts vector from 0
	// parts[i] contains configuration mask for partition id i+1
	vector< ipartitions_t > parts;
	parts.resize(egraph.getNofPartitions(),0);

	// Visit the tree in topological order bottom up and compute the configurations
	std::deque<InterpolationTree*> q;
	set<int> visited;

	q.push_back(it);
	do
	{
		InterpolationTree* node = q.front();
		q.pop_front();
		int pid = node->getPartitionId();
		//cerr << "Trying parent " << pid << endl;
		if(visited.find(pid) == visited.end())
		{
			bool children_visited = true;
			// Make sure all children have been visited, otherwise push them in the queue
			for( set< periplo::InterpolationTree* >::iterator it = node->getChildren().begin(); it != node->getChildren().end(); it++)
			{
				int cid =  (*it)->getPartitionId();
				if(visited.find(cid)==visited.end())
				{
					children_visited = false;
					q.push_back((*it));
					//cerr << "Enqueuing " << cid << endl;
				}
			}
			// All children have been visited
			if(children_visited)
			{
				//cerr << "Visiting " << pid << endl;
				visited.insert(pid);
				// Compute configuration for this node: A should include the node and the subtree rooted in it
				// In practice the mask is the logical or of the children masks plus the current node
				for( set< periplo::InterpolationTree* >::iterator it = node->getChildren().begin(); it != node->getChildren().end(); it++)
				{
					int cid = (*it)->getPartitionId();
					orbit( parts[pid-1], parts[pid-1], parts[cid-1] );
				}
				setbit( parts[pid-1], pid );
				//cerr << "Partition ids in A for configuration " << pid-1 << ": ";
				//cerr << parts[pid-1].get_str(2) << " ";
				//cerr << endl;
			}
			else
			{
				//cerr << "Enqueuing " << pid << endl;
				q.push_back(node);
			}
		}
	}
	while(!q.empty());

	produceMultipleInterpolants( parts, interpolants );
	bool property_holds = true;
	if( enabledInterpVerif() ) property_holds = verifyTreeInterpolantsFromLeaves( it, interpolants );
	return property_holds;
}



/**************** MAIN INTERPOLANTS GENERATION METHODS ************************/


void ProofGraph::produceSingleInterpolant( vector<Enode*>& interpolants )
{
	if( verbose() ) cerr << "# Single interpolant " << endl;
	unsigned npart = egraph.getNofPartitions();
	assert(npart==2);

	// Check
	checkInterAlgo();
	if( config.proof_set_inter_algo == 3 )
	{
#ifndef FULL_LABELING
		periplo_warning("Please compile with --enable-fulllabeling to enable minimal interpolation");
		return;
#endif
	}

	ipartitions_t A_mask = 0;
	// Set 1_th bit to 1 (bit 0 is untouched)
	setbit(A_mask,1);

#ifdef FULL_LABELING
	// Track AB class variables and associate index to them in nodes bit masks
	computeABVariablesMapping( A_mask );
#endif

	// NOTE generation of interpolants in CNF
	if( interpolantInCNF() )
	{
#ifdef FULL_LABELING
		if( usingMcMillanInterpolation() )
		{
			if ( verbose() > 0 ) cerr << "# Proof transformation for interpolants (partially) in CNF" << endl;
			fillProofGraph();
			proofTransformAndRestructure(-1,-1,true, &ProofGraph::handleRuleApplicationForCNFinterpolant);
			checkProof(true);
			// Normalize antecedents order ( for interpolation )
			normalizeAntecedentOrder();
			emptyProofGraph();
			printRuleApplicationStatus();
		}
		else
		{
			periplo_warning("Please set McMillan interpolation algorithm to generate interpolants in CNF");
		}
#else
		periplo_warning("Please compile with --enable-fulllabeling to enable proof transformation for interpolants in CNF");
#endif
	}
	// NOTE Preliminary application of A2 rules to strengthen/weaken the interpolant
	// Not compatible with interpolants in CNF
	else if( restructuringForStrongerInterpolant() || restructuringForWeakerInterpolant() )
	{
		if ( verbose() > 0 && restructuringForStrongerInterpolant() ) cerr << "# Preliminary A2 rules application to strengthen interpolants" << endl;
		if ( verbose() > 0 && restructuringForWeakerInterpolant() ) cerr << "# Preliminary A2 rules application to weaken interpolants" << endl;
		fillProofGraph();
		// NOTE Only a couple of loops to avoid too much overhead
		proofTransformAndRestructure(-1,2,true, &ProofGraph::handleRuleApplicationForStrongerWeakerInterpolant, A_mask);
		// Normalize antecedents order ( for interpolation )
		normalizeAntecedentOrder();
		emptyProofGraph();
	}

	// Clause and partial interpolant
	ProofNode * n;
	Enode * partial_interp;

	// Vector for topological ordering
	vector< clauseid_t > DFSv;
	// Compute topological sorting of graph
	topolSortingTopDown( DFSv );
	size_t proof_size = DFSv.size();

	// Degenerate proof
	if( proof_size==1 ) periplo_error("Degenerate proof, only empty clause - Cannot calculate interpolants");
	if( verbose() > 0 ) cerr << "# Generating interpolant " << endl;

	// Traverse proof and compute current interpolant
	for( size_t i = 0 ; i < proof_size ; i++ )
	{
		n = getNode( DFSv[ i ] ); assert(n);
		// Generate partial interpolant for clause i
		if(n->isLeaf())
		{
			if(n->getType() != CLAORIG) periplo_error( "Clause is not original" );
#ifdef FULL_LABELING
			partial_interp = compInterpLabelingOriginal( n, A_mask );
			if ( enabledPedInterpVerif() ) verifyPartialInterpolantFromLeaves( n, A_mask );
#else
			partial_interp = compInterpLabelingOriginalSimple( n, A_mask );
#endif
		}
		else
		{
#ifdef FULL_LABELING
			partial_interp = compInterpLabelingInner( n );
#else
			partial_interp = compInterpLabelingInnerSimple( n, A_mask );
#endif
		}
		assert( partial_interp );
		n->setPartialInterpolant( partial_interp );
	}
	// Last clause visited is the empty clause with total interpolant
	assert(partial_interp == getRoot()->getPartialInterpolant());
	if( verbose() ) getComplexityInterpolant(partial_interp);
	if ( enabledInterpVerif() ) verifyPartialInterpolantFromLeaves( getRoot(), A_mask );
	Enode* interpol = getRoot()->getPartialInterpolant();
	assert(interpol);

	interpolants.push_back( interpol );
}

void ProofGraph::produceMultipleInterpolants( vector< ipartitions_t >& configs,vector<Enode*> & sequence_of_interpolants )
{
/*	if( verbose() > 1 )
	{
		// Check configurations
		for(unsigned u = 0; u < configs.size(); u++)
		{
			cerr << "Partition ids in A for configuration " << u << ": ";
			cerr << configs[u].get_str(2) << " ";
			cerr << endl;
		}
	}*/

	// Check
	checkInterAlgo();
	if( config.proof_set_inter_algo == 3 )
	{
#ifndef FULL_LABELING
		periplo_warning("Please compile with --enable-fulllabeling to enable minimal interpolation");
		return;
#endif
	}

	uint64_t mem_used = 0;
	if( verbose() )
	{
		mem_used = memUsed();
		//reportff( "# Memory used before generating interpolants: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}
	assert( sequence_of_interpolants.size( ) == 0 );

	// Clause and partial interpolant
	ProofNode * n;
	Enode * partial_interp;

	// Vector for topological ordering
	vector< clauseid_t > DFSv;
	// Compute topological sorting of graph
	topolSortingTopDown( DFSv );
	size_t proof_size = DFSv.size();

	// Degenerate proof
	if(proof_size==1) periplo_error("Degenerate proof, only empty clause - Cannot calculate interpolants");

	for( unsigned curr_interp = 0; curr_interp < configs.size(); curr_interp ++ )
	{
		if( verbose() > 0 ) cerr << "# Generating interpolant " << curr_interp << endl;

		ipartitions_t& A_mask = configs[curr_interp];

#ifdef FULL_LABELING
		// Track AB class variables and associate index to them in nodes bit masks
		computeABVariablesMapping( A_mask );
#endif

		// Traverse proof and compute current interpolant
		for( size_t i = 0 ; i < proof_size ; i++ )
		{
			n = getNode( DFSv[ i ] ); assert(n);
			// Generate partial interpolant for clause i
			if(n->isLeaf())
			{
				if(n->getType() != CLAORIG) periplo_error( "Clause is not original" );
#ifdef FULL_LABELING
				partial_interp = compInterpLabelingOriginal( n, A_mask, curr_interp );
				if ( enabledPedInterpVerif() ) verifyPartialInterpolantFromLeaves( n, A_mask );
#else
				partial_interp = compInterpLabelingOriginalSimple( n, A_mask );
#endif
			}
			else
			{
#ifdef FULL_LABELING
				partial_interp = compInterpLabelingInner( n );
#else
				partial_interp = compInterpLabelingInnerSimple( n, A_mask );
#endif
			}
			assert( partial_interp );
			n->setPartialInterpolant( partial_interp );
		}
		// Last clause visited is the empty clause with total interpolant
		sequence_of_interpolants.push_back( partial_interp );
		assert(partial_interp == getRoot()->getPartialInterpolant());
		if( verbose() ) getComplexityInterpolant(partial_interp);
		if ( enabledInterpVerif() ) verifyPartialInterpolantFromLeaves( getRoot(), A_mask );

		if( verbose() )
		{
			mem_used = memUsed();
			//cerr << "# Interpolant: " << partial_interp << endl;
			//reportff( "# Memory used after generating %d interpolants: %.3f MB\n", curr_interp+1,  mem_used == 0 ? 0 : mem_used / 1048576.0 );
		}
		if ( printProofDotty( ) == 1 )
		{
			char buf[ 32 ];
			sprintf( buf, "proof_interp_%d.dot", curr_interp );
			ofstream dotty( buf );
			printProofAsDotty( dotty, A_mask );
		}
	}
}

/********** SIMPLE INTERPOLATION WITHOUT FULL LABELING **********/

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
Enode * ProofGraph::compInterpLabelingOriginalSimple( ProofNode * n, const ipartitions_t & A_mask )
{
	if(! ( usingMcMillanInterpolation( ) || usingPudlakInterpolation( ) || usingMcMillanPrimeInterpolation( ) ) )
		periplo_error_();

	icolor_t clause_color = getClauseColor( n->getInterpPartitionMask(), A_mask );
	// Original leaves can be only of class A or B
	assert( clause_color == I_A || clause_color == I_B );

	Enode * partial_interp = NULL;
	// Leaf belongs to A
	if( clause_color == I_A )
	{
		// McMillan: compute clause restricted to AB
		if( usingMcMillanInterpolation( ) )
		{
			vector< Lit > restricted_clause;
			icolor_t var_class;
			vector< Lit > & cl = n->getClause();
			const size_t size = cl.size( );
			for( size_t i = 0 ; i < size ; i ++ )
			{
				var_class = getVarClass( var(cl[i]), A_mask );
				if( var_class == I_AB ) restricted_clause.push_back( cl[i] );
			}
			size_t clause_size = restricted_clause.size( );

			//Create enode for the restricted clause
			if( clause_size == 0 )
				//Partial interpolant is false in case of empty clause left
				partial_interp = egraph.mkFalse( );
			else
			{
				//Initialize with first literal
				partial_interp = thandler->varToEnode(var(restricted_clause[0]));
				//Check polarity literal
				if(sign(restricted_clause[0])) partial_interp = egraph.mkNot(egraph.cons(partial_interp));

				Enode * lit;
				for(size_t i=1;i<clause_size;i++)
				{
					lit = thandler->varToEnode(var(restricted_clause[i]));
					//Check polarity literal
					if(sign(restricted_clause[i])) lit = egraph.mkNot(egraph.cons(lit));
					//Build adding literals progressively
					partial_interp = egraph.mkOr(egraph.cons(partial_interp, egraph.cons(lit)));
				}
			}
		}
		// Pudlak or McMillan': false
		else
		{
			partial_interp = egraph.mkFalse( );
		}
	}
	// Leaf belongs to B
	else if( clause_color == I_B )
	{
		//  McMillan': compute clause restricted to a
		if( usingMcMillanPrimeInterpolation( ) )
		{
			vector< Lit > restricted_clause;
			icolor_t var_class;
			vector< Lit > & cl = n->getClause();
			const size_t size = cl.size( );
			for( size_t i = 0 ; i < size ; i ++ )
			{
				var_class = getVarClass( var(cl[i]), A_mask );
				if( var_class == I_AB ) restricted_clause.push_back( cl[i] );
			}
			size_t clause_size = restricted_clause.size( );

			// Create enode for the restricted clause
			if( clause_size == 0 )
				// Partial interpolant is true (negation of false) in case of empty clause left
				partial_interp = egraph.mkTrue( );
			else
			{
				// Remember that we are negating the restricted clause!
				// Literals change polarity and we build an and of literals
				// Initialize with first literal
				partial_interp = thandler->varToEnode( var( restricted_clause[0] ) );
				// Check polarity literal
				if( !sign( restricted_clause[0] ) )
					partial_interp = egraph.mkNot( egraph.cons( partial_interp ) );

				Enode * lit = NULL;
				for( size_t i = 1 ; i < clause_size ; i++ )
				{
					lit = thandler->varToEnode( var( restricted_clause[i] ) );
					// Check polarity literal
					if( !sign( restricted_clause[i] ) )
						lit = egraph.mkNot( egraph.cons( lit ) );
					// Build adding literals progressively
					partial_interp = egraph.mkAnd( egraph.cons( partial_interp, egraph.cons( lit ) ) );
				}
			}
		}
		// Pudlak or McMillan': true
		else
		{
			partial_interp = egraph.mkTrue( );
		}
	}
	else periplo_error( "Clause has no color" );

	return partial_interp;
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
Enode * ProofGraph::compInterpLabelingInnerSimple( ProofNode * n, const ipartitions_t & A_mask )
{
	if(! ( usingMcMillanInterpolation( ) || usingPudlakInterpolation( ) || usingMcMillanPrimeInterpolation( ) ) )
		periplo_error_();

	// Get antecedents partial interpolants
	Enode * partial_interp_ant1 = n->getAnt1()->getPartialInterpolant();
	Enode * partial_interp_ant2 = n->getAnt2()->getPartialInterpolant();
	assert( partial_interp_ant1 ); assert( partial_interp_ant2 );

	Enode * partial_interp = NULL;
	// Determine class pivot
	icolor_t pivot_class = getVarClass( n->getPivot(), A_mask );

	// Pivot class A -> interpolant = interpolant of ant1 OR interpolant of ant2
	if( pivot_class == I_A )
	{
		partial_interp = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
	}
	// Pivot class B -> interpolant = interpolant of ant1 AND interpolant of ant2
	else if ( pivot_class == I_B )
	{
		partial_interp = egraph.mkAnd( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
	}
	// Pivot class AB ->
	// 1) Pudlak interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
	// 1) Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
	// 2) McMillan interpolant  = interpolant of ant1 AND interpolant of ant2
	// 3) McMillan' interpolant = interpolant of ant1 OR interpolant of ant2
	else if ( pivot_class == I_AB)
	{
		if( usingPudlakInterpolation( ) )
		{
			// Find pivot occurrences in ant1 and ant2 and create enodes
			Var piv_ = n->getPivot();
			//cerr << "Inserting: " << thandler->varToEnode(piv_) << " " << piv_ << endl;
			Enode* piv = thandler->varToEnode( piv_ );
			bool choose_alternative = false;
			if ( usingAlternativeInterpolant() ) choose_alternative = decideOnAlternativeInterpolation( n );

			// Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
			if( choose_alternative )
			{
				Enode * and_1 = egraph.mkAnd( egraph.cons( partial_interp_ant1, egraph.cons( egraph.mkNot( egraph.cons( piv ) ) ) ) );
				Enode * and_2 = egraph.mkAnd( egraph.cons( partial_interp_ant2, egraph.cons( piv ) ) );
				partial_interp = egraph.mkOr( egraph.cons( and_1, egraph.cons( and_2 ) ) );
				// TODO ~piv \/ piv is not simplified, but should be!
				assert(partial_interp != egraph.mkTrue());
			}
			// Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
			else
			{
				Enode * or_1 = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( piv ) ) );
				Enode * or_2 = egraph.mkOr( egraph.cons( partial_interp_ant2, egraph.cons( egraph.mkNot( egraph.cons( piv ) ) ) ) );
				partial_interp = egraph.mkAnd( egraph.cons( or_1, egraph.cons( or_2 ) ) );
				// TODO piv /\ ~piv is not simplified, but should be!
				assert(partial_interp != egraph.mkFalse());
			}
		}
		else if ( usingMcMillanInterpolation( ) )
		{
			partial_interp = egraph.mkAnd( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
		}
		else if ( usingMcMillanPrimeInterpolation( ) )
		{
			partial_interp = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
		}
	}
	else periplo_error( "Pivot has no class" );

	return partial_interp;
}

void ProofGraph::checkInterAlgo()
{
	if ( !( usingMcMillanInterpolation()
			|| usingPudlakInterpolation()
			|| usingMcMillanPrimeInterpolation()
			||  usingMinimalInterpolation()
			|| config.proof_set_inter_algo == 4))
		periplo_error( "Please choose 0/1/2/3/4 as values for proof_set_inter_algo");

	if ( verbose() > 0 )
	{
		if( usingPudlakInterpolation() )
			cerr << "# Using Pudlak interpolation" << endl;
		else if( usingMcMillanInterpolation() )
			cerr << "# Using McMillan interpolation" << endl;
		else if( usingMcMillanPrimeInterpolation() )
			cerr << "# Using McMillan' interpolation" << endl;
		else if(  usingMinimalInterpolation() )
			cerr << "# Using minimal interpolation" << endl;
		else if( config.proof_set_inter_algo == 4 )
			cerr << "# Using labeling suggestions interpolation" << endl;
	}
}


/********** FULL LABELING BASED INTERPOLATION **********/

#ifdef FULL_LABELING

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
Enode * ProofGraph::compInterpLabelingOriginal( ProofNode * n, const ipartitions_t & A_mask, unsigned num_config )
{
	// First set labeling for AB class literals
	// McMillan's system
	if( usingMcMillanInterpolation( ) ) setLeafMcMillanLabeling( n );
	// Symmetric system
	else if( usingPudlakInterpolation( ) ) setLeafPudlakLabeling( n );
	// McMillan's prime system
	else if( usingMcMillanPrimeInterpolation( ) ) setLeafMcMillanPrimeLabeling( n );
	// Minimal interpolation labeling
	else if( usingMinimalInterpolation() ) setLeafMinimalInterpolantLabeling( n, A_mask );
	// Labeling suggestions enabled
	else if( usingLabelingSuggestions( ) ) setLabelingFromMap( n, num_config );
	// Error
	else periplo_error( "No interpolation algorithm chosen" );

	// Then calculate interpolant
	icolor_t clause_color = getClauseColor( n->getInterpPartitionMask(), A_mask );

	// Original leaves can be only of class A or B
	assert( clause_color == I_A || clause_color == I_B );

	Enode * partial_interp = NULL;
	// Leaf belongs to A -> interpolant = leaf clause restricted to b
	if( clause_color == I_A )
	{
		//Compute clause restricted to b

		vector< Lit > restricted_clause;
		// In labeling, classes and colors are distinct
		icolor_t var_class;
		icolor_t var_color;
		vector< Lit > & cl = n->getClause();
		const size_t size = cl.size( );
		for( size_t i = 0 ; i < size ; i ++ )
		{
			Var v = var(cl[i]);
			var_class = getVarClass2( v );
			assert( var_class == I_B || var_class == I_A || var_class == I_AB );
			if( var_class == I_B || var_class == I_A ) var_color = var_class;
			else
			{
				// Determine color of AB variable
				if( isColoredA( n,v ) ) var_color = I_A;
				else if ( isColoredB( n,v )  ) var_color = I_B;
				else if ( isColoredAB( n,v ) ) var_color = I_AB;
				else periplo_error( "Variable " << v << " has no color in clause " << n->getId() );
			}
			if( var_color == I_B ) restricted_clause.push_back( cl[i] );
		}
		size_t clause_size = restricted_clause.size( );

		//Create enode for the restricted clause
		if( clause_size == 0 )
			//Partial interpolant is false in case of empty clause left
			partial_interp = egraph.mkFalse( );
		else
		{
			//Initialize with first literal
			partial_interp = thandler->varToEnode(var(restricted_clause[0]));
			//Check polarity literal
			if(sign(restricted_clause[0])) partial_interp = egraph.mkNot(egraph.cons(partial_interp));

			Enode * lit;
			for(size_t i=1;i<clause_size;i++)
			{
				lit = thandler->varToEnode(var(restricted_clause[i]));
				//Check polarity literal
				if(sign(restricted_clause[i])) lit = egraph.mkNot(egraph.cons(lit));
				//Build adding literals progressively
				partial_interp = egraph.mkOr(egraph.cons(partial_interp, egraph.cons(lit)));
			}
		}
	}
	// Leaf belongs to B -> interpolant = negation of leaf clause restricted to a
	else if( clause_color == I_B )
	{
		//Compute clause restricted to a

		vector< Lit > restricted_clause;
		// In labeling, classes and colors are distinct
		icolor_t var_class;
		icolor_t var_color;
		vector< Lit > & cl = n->getClause();
		const size_t size = cl.size( );
		for( size_t i = 0 ; i < size ; i ++ )
		{
			Var v = var(cl[i]);
			var_class = getVarClass2( v );
			assert( var_class == I_B || var_class == I_A || var_class == I_AB );
			if( var_class == I_B || var_class == I_A ) var_color = var_class;
			else
			{
				// Determine color of AB variable
				if( isColoredA( n,v ) ) var_color = I_A;
				else if ( isColoredB( n,v )  ) var_color = I_B;
				else if ( isColoredAB( n,v ) ) var_color = I_AB;
				else periplo_error( "Variable " << v << " has no color in clause " << n->getId() );
			}
			if( var_color == I_A ) restricted_clause.push_back( cl[i] );
		}
		size_t clause_size = restricted_clause.size( );

		// Create enode for the restricted clause
		if( clause_size == 0 )
			// Partial interpolant is true (negation of false) in case of empty clause left
			partial_interp = egraph.mkTrue( );
		else
		{
			// Remember that we are negating the restricted clause!
			// Literals change polarity and we build an and of literals
			// Initialize with first literal
			partial_interp = thandler->varToEnode( var( restricted_clause[0] ) );
			// Check polarity literal
			if( !sign( restricted_clause[0] ) )
				partial_interp = egraph.mkNot( egraph.cons( partial_interp ) );

			Enode * lit = NULL;
			for( size_t i = 1 ; i < clause_size ; i++ )
			{
				lit = thandler->varToEnode( var( restricted_clause[i] ) );
				// Check polarity literal
				if( !sign( restricted_clause[i] ) )
					lit = egraph.mkNot( egraph.cons( lit ) );
				// Build adding literals progressively
				partial_interp = egraph.mkAnd( egraph.cons( partial_interp, egraph.cons( lit ) ) );
			}
		}
	}
	else periplo_error( "Clause has no color" );

	return partial_interp;
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
Enode * ProofGraph::compInterpLabelingInner( ProofNode * n )
{
	// Get antecedents partial interpolants
	Enode * partial_interp_ant1 = n->getAnt1()->getPartialInterpolant();
	Enode * partial_interp_ant2 = n->getAnt2()->getPartialInterpolant();
	assert( partial_interp_ant1 ); assert( partial_interp_ant2 );

	Enode * partial_interp = NULL;
	// Determine color pivot, depending on its color in the two antecedents
	icolor_t pivot_color = getPivotColor( n );

	// Pivot colored a -> interpolant = interpolant of ant1 OR interpolant of ant2
	if( pivot_color == I_A)
	{
		partial_interp = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
	}
	// Pivot colored b -> interpolant = interpolant of ant1 AND interpolant of ant2
	else if ( pivot_color == I_B )
	{
		partial_interp = egraph.mkAnd( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
	}
	// Pivot colored ab -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
	// Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
	else if ( pivot_color == I_AB)
	{
		// Find pivot occurrences in ant1 and ant2 and create enodes
		Var piv_ = n->getPivot();
		//cerr << "Inserting: " << thandler->varToEnode(piv_) << " " << piv_ << endl;
		Enode* piv = thandler->varToEnode( piv_ );
		bool choose_alternative = false;
		if ( usingAlternativeInterpolant() ) choose_alternative = decideOnAlternativeInterpolation( n );

		// Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
		if( choose_alternative )
		{
			Enode * and_1 = egraph.mkAnd( egraph.cons( partial_interp_ant1, egraph.cons( egraph.mkNot( egraph.cons( piv ) ) ) ) );
			Enode * and_2 = egraph.mkAnd( egraph.cons( partial_interp_ant2, egraph.cons( piv ) ) );
			partial_interp = egraph.mkOr( egraph.cons( and_1, egraph.cons( and_2 ) ) );

			// TODO ~piv \/ piv is not simplified, but should be!
			assert(partial_interp != egraph.mkTrue());
		}
		// Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
		else
		{
			Enode * or_1 = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( piv ) ) );
			Enode * or_2 = egraph.mkOr( egraph.cons( partial_interp_ant2, egraph.cons( egraph.mkNot( egraph.cons( piv ) ) ) ) );
			partial_interp = egraph.mkAnd( egraph.cons( or_1, egraph.cons( or_2 ) ) );

			// TODO piv /\ ~piv is not simplified, but should be!
			assert(partial_interp != egraph.mkFalse());
		}
	}
	else periplo_error( "Pivot has no color" );

	return partial_interp;
}

void ProofGraph::setLeafPudlakLabeling( ProofNode* n )
{
	// Reset labeling
	resetLabeling( n );

	vector< Lit > & cl = n->getClause();
	for( unsigned i=0; i < cl.size(); i++)
	{
		Var v = var(cl[i]);
		icolor_t var_class = getVarClass2( v );
		// Color AB class variables as ab
		if( var_class == I_AB ) colorAB(n,v);
		else if ( var_class == I_A || var_class == I_B );
		else periplo_error( "Variable has no class" );
	}
}

void ProofGraph::setLeafMcMillanLabeling( ProofNode* n )
{
	// Reset labeling
	resetLabeling(n);

	vector< Lit > & cl = n->getClause();
	for( unsigned i=0; i < cl.size(); i++)
	{
		Var v = var(cl[i]);
		icolor_t var_class = getVarClass2( v );
		// Color AB class variables as b
		if( var_class == I_AB ) colorB(n,v);
		else if ( var_class == I_A || var_class == I_B );
		else periplo_error( "Variable has no class" );
	}
}

void ProofGraph::setLeafMcMillanPrimeLabeling( ProofNode* n )
{
	// Reset labeling
	resetLabeling(n);

	vector< Lit > & cl = n->getClause();
	for( unsigned i=0; i < cl.size(); i++)
	{
		Var v = var(cl[i]);
		icolor_t var_class = getVarClass2( v );
		// Color AB class variables a if clause is in A
		if( var_class == I_AB ) colorA(n,v);
		// Color AB class variables b if clause is in B
		else if ( var_class == I_A || var_class == I_B );
		else periplo_error( "Variable has no class" );
	}
}

void ProofGraph::setLeafMinimalInterpolantLabeling( ProofNode* n, const ipartitions_t & A_mask )
{
	// Reset labeling
	resetLabeling(n);
	// Determine whether clause is in A or in B
	icolor_t clause_color = getClauseColor( n->getInterpPartitionMask(), A_mask );
	assert( clause_color == I_A || clause_color == I_B );

	vector< Lit > & cl = n->getClause();
	for( unsigned i=0; i < cl.size(); i++)
	{
		Var v = var(cl[i]);
		icolor_t var_class = getVarClass2( v );
		if( var_class == I_AB )
		{
			// Color AB class variables a if clause is in A
			if ( clause_color == I_A ) colorA(n,v);
			// Color AB class variables b if clause is in B
			else if ( clause_color == I_B ) colorB(n,v);
		}
		else if ( var_class == I_A || var_class == I_B );
		else periplo_error( "Variable has no class" );
	}
}

void ProofGraph::setLabelingFromMap	( ProofNode* n, unsigned num_config )
{
	assert(vars_suggested_color_map);
	// Reset labeling
	resetLabeling(n);

	vector< Lit > & cl = n->getClause();
	for( unsigned i=0; i < cl.size(); i++)
	{
		Var v = var(cl[i]);
		icolor_t var_class = getVarClass2( v );
		// Color AB class variables as a
		if( var_class == I_AB )
		{
			// Retrieve correspondent Enode
			Enode* en = thandler->varToEnode(v);
			std::map<Enode*, icolor_t>* col_map = (*vars_suggested_color_map)[num_config];
			assert(col_map);
			std::map<Enode*, icolor_t>::iterator it=col_map->find(en);
			if( it == col_map->end() )
			{
				cerr << "Color suggestion for " << en << " not found; using Pudlak" << endl;
				colorAB(n,v);
			}
			else
			{
				icolor_t color = it->second;
				if(color == I_A) colorA(n,v);
				else if(color == I_B) colorB(n,v);
				else if(color == I_AB) colorAB(n,v);
				else periplo_error_();
			}
		}
		else if ( var_class == I_A || var_class == I_B );
		else periplo_error( "Variable has no class" );
	}
}
#endif

#endif
