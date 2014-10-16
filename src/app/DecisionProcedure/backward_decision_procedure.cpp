/*****************************************************************************
 *  dWiNA - Deciding WSkS using non-deterministic automata
 *
 *  Copyright (c) 2014  Tomas Fiedor <ifiedortom@fit.vutbr.cz>
 *
 *  Description:
 *    WSkS Decision Procedure
 *
 *****************************************************************************/

#include <boost/dynamic_bitset.hpp>

#include "environment.hh"
#include "decision_procedures.hh"
#include "containers/NewStateSet.hh"

// #define DEBUG_BDP
//#define DEBUG_PREFIX
#define PRUNE_BY_SUBSUMPTION

// #define DEBUG_REMOVE_ALL

// Global Variables

#ifdef USE_BDDCACHE
extern MultiLevelMCache<MacroTransMTBDDNew> BDDCache;
#endif

/**
 * Constructs new initial state for the final automaton, according to the
 * number of determinizations that we are going to need.
 *
 * @param aut: matrix automaton
 * @param numberOfDeterminizations: how many levels we will need
 * @return initial state of the final automaton
 */
StateType constructInitialStateNew(
	const Automaton&       aut,
	unsigned               numberOfDeterminizations)
{
	// Getting initial states
	SetOfStates states;
	for (auto state : aut.GetFinalStates()) {
		states.insert(state);
	}

	// now add some levels
	StateType ithState;
	while (numberOfDeterminizations != 0){
		ithState = NewStateSet::GetUniqueSetHandle(states);
		states.clear();
		states.insert(ithState);
		--numberOfDeterminizations;
	}

	return ithState;
}

/// returns the last variable to remain after projection (all lower should be removed)
size_t getProjectionVariableNew(
	const PrefixListType&     prefix,
	size_t                    level)
{
	assert(level < prefix.size());

	const VariableSet& varSet = prefix[level];
	assert(!varSet.empty());
	size_t maxVarIndex = varSet[0];
	for (size_t var : varSet)
	{
		if (var > maxVarIndex)
		{
			maxVarIndex = var;
		}
	}

	return maxVarIndex + 1;
}

/**
 * Generates post of @p state, by constructing posts of lesser level and
 * doing the union of these states with projection over the prefix
 *
 * @param aut: base automaton
 * @param state: initial state we are generating post for
 * @param level: level of inception
 * @param prefix: list of variables for projection
 * @return MTBDD representing the post of the state @p state
 */
MacroTransMTBDDNew GetMTBDDForPostNew(
	const Automaton&          aut,
	StateType                 state,
	unsigned                  level,
	const PrefixListType&     prefix)
{
// #ifdef DEBUG_BDP
// 		std::cerr << "[GetMTBDDForPostNew] state = " << state << "\n";
// 		std::cerr << "[GetMTBDDForPostNew] level = " << level << "\n";
// #endif

	// Convert MTBDD from VATA to MacroStateRepresentation
	if (level == 0)
	{	// 'state' is a real state
		const TransMTBDD* stateTransition = getMTBDDForStateTuple(aut, Automaton::StateTuple({state}));

		size_t projecting = getProjectionVariableNew(prefix, level);
		assert(projecting > 0);

#ifdef DEBUG_BDP
		std::cerr << "[GetMTBDDForPostNew]<level0> projecting over var < " << projecting << "\n";
#endif

		AdditionApplyFunctor adder;
		TransMTBDD projected = stateTransition->Project(
			[projecting](size_t var) {return var < projecting;}, adder);

		// TODO: cache the result?
		StateDeterminizatorFunctorNew sdf;

		return sdf(projected);
	}
	else
	{
		size_t projecting = getProjectionVariableNew(prefix, level);

		// no constant reference because the hash table may rellocate!
		SetOfStates states = NewStateSet::GetSetForHandle(state);
// #ifdef DEBUG_BDP
// 		std::cerr << "[GetMTBDDForPostNew] processing set: ";
// 		NewStateSet::DumpSetOfStates(std::cerr, states, level);
// 		std::cerr << "\n";
// #endif

		MacroTransMTBDDNew resMtbdd(NewStateSet::GetUniqueSetHandle(SetOfStates()));
		MacroPrunedUnionFunctorNew muf(level);

		for (StateType itState : states)
		{
#ifdef DEBUG_BDP
			std::cerr << "[GetMTBDDForPostNew] processing nested state: ";
			NewStateSet::DumpHandle(std::cerr, itState, level-1);
			std::cerr << "\n";
#endif
			MacroTransMTBDDNew nextPost = GetMTBDDForPostNew(aut, itState, level - 1, prefix);
#ifdef DEBUG_BDP
			std::cerr << "[GetMTBDDForPostNew] projection for state: ";
			NewStateSet::DumpHandle(std::cerr, itState, level-1);
			std::cerr << "\n";
			std::cerr << "[GetMTBDDForPostNew]<level" << level
				<< "> projecting over var < " << projecting << "\n";
#endif
			// MacroTransMTBDDNew projected = nextPost.Project(
			// 	[projecting](size_t var) {return var < projecting;}, muf);
#ifdef DEBUG_BDP
			std::cerr << "[GetMTBDDForPostNew] union for state: ";
			NewStateSet::DumpHandle(std::cerr, itState, level-1);
			std::cerr << "\n";
#endif
			// resMtbdd = muf(resMtbdd, projected);
			resMtbdd = muf(resMtbdd, nextPost);
		}

#ifdef DEBUG_BDP
		std::cerr << "[GetMTBDDForPostNew] nested states processed\n";
#endif

		MacroStateDeterminizatorFunctorNew msdf;
		resMtbdd = msdf(resMtbdd);

		return resMtbdd;
	}
}

std::string prefixToString(const PrefixListType& prefix)
{
	std::ostringstream os;

	for (const VariableSet& varSet : prefix)
	{
		os << "[";
		for (auto it = varSet.begin(); it != varSet.end(); ++it)
		{
			if (it != varSet.begin())
			{
				os << ", ";
			}
			os << *it;
		}
		os << "]";
	}

	return os.str();
}

Automaton::SymbolType constructZeroTrack(
	const PrefixListType&     prefix,
	size_t                    level)
{
	size_t maxVar = 0;
	for (const VariableSet& varSet : prefix)
	{
		for (size_t var : varSet)
		{
			if (var > maxVar)
			{
				maxVar = var;
			}
		}
	}

	size_t projVar = getProjectionVariableNew(prefix, level);

#ifdef DEBUG_BDP
	std::cerr << "[constructZeroTrack] projection variable  = " << projVar << "\n";
#endif

	Automaton::SymbolType zeroTrack(maxVar+1);

	for (size_t i = projVar; i < maxVar+1; ++i)
	{
		zeroTrack.SetIthVariableValue(i, Automaton::SymbolType::ZERO);
	}

#ifdef DEBUG_BDP
	std::cerr << "[constructZeroTrack] zeroTrack = " << zeroTrack.ToString() << "\n";
#endif

	return zeroTrack;
}


/**
 * Constructs a post through zero tracks for backwards procedure which is
 * a little bit different to handle.
 *
 * @param aut: base automaton
 * @param state: initial state we are getting zero post for
 * @param level: level of macro inception
 * @param prefix: list of variables for projection
 * @return zero post of initial @p state
 */
StateType GetZeroMacroPostNew(
	const Automaton&          aut,
	StateType                 state,
	unsigned                  level,
	const PrefixListType&     prefix)
{
#ifdef DEBUG_BDP
	std::cerr << "[GetZeroMacroPostNew] state = ";
	NewStateSet::DumpHandle(std::cerr, state, level);
	std::cerr << "\n";
	std::cerr << "[GetZeroMacroPostNew] level = " << level << "\n";
	std::cerr << "[GetZeroMacroPostNew] prefix = ";
	std::cerr << prefixToString(prefix);
	std::cerr << "\n";
#endif

	if (level == 0)
	{
		MacroTransMTBDDNew transPost = GetMTBDDForPostNew(aut, state, level, prefix);
		StateType postStates = transPost.GetValue(constructZeroTrack(prefix, level));

#ifdef DEBUG_BDP
		std::cerr << "[GetZeroMacroPostNew] postStates = ";
		NewStateSet::DumpHandle(std::cerr, postStates, level+1);
		std::cerr << "\n";
#endif

		return postStates;
	}
	else
	{
		MacroTransMTBDDNew transPost = GetMTBDDForPostNew(aut, state, level, prefix);
		MacroPrunedUnionFunctorNew muf(level+1);

		size_t projecting = getProjectionVariableNew(prefix, level);

		MacroTransMTBDDNew projectedMtbdd = transPost.Project(
			[projecting](size_t var) { return var < projecting;}, muf);

		Automaton::SymbolType zeroSymb = constructZeroTrack(prefix, level);
#ifdef DEBUG_BDP
		std::cerr << "[GetZeroMacroPostNew] zeroTrack = " << zeroSymb.ToString() << "\n";
#endif
		StateType postStates = projectedMtbdd.GetValue(zeroSymb);

#ifdef DEBUG_BDP
		std::cerr << "[GetZeroMacroPostNew] postStates = ";
		NewStateSet::DumpHandle(std::cerr, postStates, level+1);
		std::cerr << "\n";
#endif

		return postStates;
	}



// 	else
// 	{
// 		if(NewStateSet::GetSetForHandle(state).size() == 0)
// 		{
// 			return NewStateSet::GetUniqueSetHandle(SetOfStates());
// 		}
// 		else
// 		{
// 			MacroTransMTBDDNew transPost = GetMTBDDForPostNew(aut, state, level, prefix);
// 			size_t projecting = getProjectionVariable(level, prefix);
// 			//MacroUnionFunctor muf;
// 			MacroPrunedUnionFunctorNew muf(level-1);
// 			MacroStateDeterminizatorFunctorNew msdf;
//
// 			MacroTransMTBDDNew projectedMtbdd = (msdf(transPost)).Project(
// 					[projecting](size_t var) { return var < projecting;}, muf);
//
// 			StateType postStates = projectedMtbdd.GetValue(constructUniversalTrack());
//
// 			return postStates;
// 		}
// 	}
}

/**
 * The core of the algorithm, the very special and superb and awesome and
 * completely mind-blowing principle of Ondra and Lukas.
 * Wow. So easy. Much power. Many admirations.
 *
 * Basically we screw the upward/downward closed structure of the generators
 * and work only with generators and computes predecessors through zero tracks.
 * Since the automaton is reversed we basically work with posts, most of which
 * is implemented in forward procedure (yay!).
 *
 * TODO: Pruning by simulation relation
 *
 * @param[in] aut: base automaton
 * @param[in] prefix: prefix, list of second-order variables
 * @param[in] detNo: number of determizations needed
 * @return: MacroState representing all final states
 */
StateType computeFinalStates(
	const Automaton&           aut,
	const PrefixListType&      prefix,
	unsigned int               detNo)
{
	NewStateSetList worklist;
	SetOfStates states;

#ifndef DEBUG_REMOVE_ALL
	std::cerr << "Runing [computeFinalStates] for determinization level: " << detNo << "\n";;
#endif

	if (detNo == 0)
	{
		// Since we are working with pre, final states are actual initial
		MTBDDLeafStateSet matrixInitialStates;
		getInitialStatesOfAutomaton(aut, matrixInitialStates);

		for (auto state : matrixInitialStates)
		{
			worklist.push_back(state);
			states.insert(state);
		}
	}
	else
	{
		StateType finalStatesBelow = computeFinalStates(aut, prefix, detNo-1);
#ifndef DEBUG_REMOVE_ALL
		std::cout << "[computeFinalStates] Dumping final states from level " << detNo - 1 << "\n";
		NewStateSet::DumpHandle(std::cerr, finalStatesBelow, detNo);
		std::cout << "\n";
#endif
		worklist.push_back(finalStatesBelow);
		states.insert(finalStatesBelow);
	}

#ifdef DEBUG_BDP
	std::cerr << "[computeFinalStates] Starting with states\n";
	NewStateSet::DumpSetOfStates(std::cerr, states, detNo+1);
	std::cerr << "\n";
#endif

	unsigned int i = 0;
	while (!worklist.empty())
	{
		StateType q = worklist.back();
		worklist.pop_back();

#ifdef DEBUG_BDP
		std::cout << "[computeFinalStates] Dumping actual working state, iteration " << i++ << "\n";
		NewStateSet::DumpHandle(std::cerr, q, detNo);
		std::cout << "\n\n";
#endif

		StateType predecessors = GetZeroMacroPostNew(aut, q, detNo, prefix);
#ifdef DEBUG_BDP
		std::cout << "[computeFinalStates] Dumping predecessor of current working state: \n";
		NewStateSet::DumpHandle(std::cerr, predecessors, detNo+1);
		std::cout << "\n";
#endif

		for(auto state : NewStateSet::GetSetForHandle(predecessors))
		{
			if (NewStateSet::AddStateToSet(states, state, detNo))
			{	// in the case the predecessor is new, push him into the workset
#ifdef DEBUG_BDP
				std::cerr << "[computeFinalStates] adding predecessor: ";
				NewStateSet::DumpHandle(std::cerr, state, detNo);
				std::cerr << "\n";
#endif
				worklist.push_back(state);
				states.insert(state);
			}
		}
	}

	StateType z = NewStateSet::GetUniqueSetHandle(states);

#ifdef DEBUG_BDP
	std::cout << "[computeFinalStates] Returning Z:";
	NewStateSet::DumpHandle(std::cerr, z, detNo+1);
	std::cout << "\n";
	std::cout << "[-----------------------------------------------------------------]\n";
#endif

	return z;
}

/**
 * Tests if initial state is in final states or not.
 *
 * Current implementation should work like this: There are two kinds of terms
 * at trees: Downward-closed Sets (DcS) and Upward Closed mit dem Krügel Operator Sets (UcS)
 * for DcS the looked-up initial state should be contain in the DcS, ergo. it is OR node,
 * and for UcS it should be completely contained, so it is AND node.
 *
 * TODO: MacroStateSet partitioning
 *
 * @param[in] initial: initial state of automaton
 * @param[in] finalStates: set of final states
 * @return: True if initial is in finalStates
 */
bool initialStateIsInFinalStates(StateType initial, StateType finalStates, unsigned int level)
{
	assert(level >= 1);

	// This probably will be more problematic than we think
	//
	if (level == 1)
	{
		// TODO: This may need some optimizations
		for (StateType finState : NewStateSet::GetSetForHandle(finalStates))
		{	// we need to cover every 'finState'
			bool isCovered = false;
			for (StateType istate : NewStateSet::GetSetForHandle(initial))
			{	// check if istate is in 'finState'
				const SetOfStates& finStateSet = NewStateSet::GetSetForHandle(finState);
				if (std::find(finStateSet.cbegin(), finStateSet.cend(), istate) != finStateSet.cend())
				{	// in case we found 'istate' in 'finStateSet'
					isCovered = true;
					break;
				}
			}
			if(!isCovered) {
				std::cout << "return false, something not covered;\n";
				return false;
			}
		}
		std::cout << "return true;\n";
		return true;
	}
	else
	{ // is singleton, so we get the first
		const SetOfStates& lowerInitialStateSet = NewStateSet::GetSetForHandle(initial);
		assert(lowerInitialStateSet.size() == 1);
		StateType newInitialStateSet = *lowerInitialStateSet.cbegin();
		if (level % 2 == 0) {
			// Downward closed
			const SetOfStates& members = NewStateSet::GetSetForHandle(finalStates);
			for(auto state : members) {
				if(initialStateIsInFinalStates(newInitialStateSet, state, level - 1)) {
					return true;
				}
			}
			return false;
		// level % 2 == 1
		} else {
			// Upward closed
			const SetOfStates& members = NewStateSet::GetSetForHandle(finalStates);
			for (auto state : members) {
				if(!initialStateIsInFinalStates(newInitialStateSet, state, level - 1)) {
					return false;
				}
			}
			return true;
		}
	}
}

/**
 * Constructs a set of final state of automaton and then tests if the initial
 * state is subset of the final states;
 *
 * @param[in] aut: base automaton
 * @param[in] prefix: list of second-order variables for projection
 */
bool testValidity(
	const Automaton&           aut,
	const PrefixListType&      prefix,
	bool                       topmostIsNegation)
{
	unsigned int determinizationNumber = prefix.size();
#ifdef DEBUG_BDP
	std::cout << "[testValidity] prefix: " << prefixToString(prefix) << "\n";
#endif

// #ifdef DEBUG_BDP
// 	VATA::Serialization::TimbukSerializer serial;
// 	std::cout << "[testValidity] automaton: " << aut.DumpToString(serial, "symbolic") << "\n";
// 	std::cout << "[testValidity] automaton: " << aut.DumpToDot() << "\n";
// #endif

	StateType initialState = constructInitialStateNew(aut, determinizationNumber);
#ifdef DEBUG_BDP
	std::cout << "[testValidity] Dumping initial state: ";
	NewStateSet::DumpHandle(std::cerr, initialState, determinizationNumber);
	std::cout << "\n";
#endif

	// compute the final set of states
	SetOfStates states;
	StateType predFinalStates = computeFinalStates(aut, prefix, determinizationNumber-1);
	states.insert(predFinalStates);
	StateType finalStates = NewStateSet::GetUniqueSetHandle(states);
	// std::cout << "[*] Size of the searched space: " << finalStates->measureStateSpace() << "\n";

#ifdef DEBUG_BDP
	std::cout << "[testvalidity] dumping computed final states:\n";
	NewStateSet::DumpHandle(std::cerr, finalStates, determinizationNumber+1);
	std::cout << "\n";
#endif

	// if initial state is in final states then validity holds
	bool result;
	if(determinizationNumber % 2 == 0) {
		result = initialStateIsInFinalStates(initialState, finalStates, determinizationNumber);
	} else {
		result = !initialStateIsInFinalStates(initialState, finalStates, determinizationNumber);
	}

	if(topmostIsNegation) {
		return result;
	} else {
		return !result;
	}
}

/**
 * Implementation of backward decision procedurefor WSkS. We try to compute
 * final sets from backwards and then test if initial state is in the set of
 * final sets to decide the formula
 *
 * @param[in] aut: base automaton (quantifier free)
 * @param[in] formulaPrefixSet: set of second-order variables corresponding to
 * 		the prefix of the closed formula phi
 * @param[in] negFormulaPrefixSet: set of second-order variables corresponding to
 * 		the prefix of the closed negation of formula phi
 * @param[in] formulaIsGround: true if formula is ground, i.e. there are no free vars
 *      Note, that for ground formula, there exists only two answers, as formula
 *      can either be valid or unsatisfiable.
 * @return: Decision procedure results
 */
int decideWS1S_backwards(
	const Automaton&         aut,
	const PrefixListType&    formulaPrefixSet,
	const PrefixListType&    negFormulaPrefixSet,
	bool                     formulaIsGround,
	bool                     topmostIsNegation)
{
	if(options.dump) {
		std::cout << "[*] Commencing backward decision procedure for WS1S\n";
	}

//#ifdef DEBUG_DP
	if(formulaIsGround) {
		std::cout << "[*] Formula is ground\n";
	} else {
		std::cout << "[*] Formula is not ground\n";
	}
//#endif

	// If formula is ground, then we only test validity/unsat and not satisfiablity
	if(formulaIsGround) {
		bool formulaIsValid = testValidity(aut, formulaPrefixSet, topmostIsNegation);
		if(formulaIsValid) {
			return VALID;
		} else {
			return UNSATISFIABLE;
		}
	// If formula is unground and closed formula is valid, then formula may still
	// be invalid, so we have to test validity of closure of negation of formula.
	// If negation of formula after closure is the negation valid, then we can
	// say, that there exists a counterexample and hence is the formula sat.
	} else {
		bool formulaIsValid = testValidity(aut, formulaPrefixSet, topmostIsNegation);
		// formula is UNSAT
		if(!formulaIsValid) {
			return UNSATISFIABLE;
		} else {
			bool formulaIsValid = !testValidity(aut, negFormulaPrefixSet, topmostIsNegation);
			if(formulaIsValid) {
				return VALID;
			} else {
				return SATISFIABLE;
			}
		}
	}
}
