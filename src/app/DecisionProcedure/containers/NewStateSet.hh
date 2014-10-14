/*****************************************************************************
 *  dWiNA - Deciding WSkS using non-deterministic automata
 *
 *  Copyright (c) 2014  Tomas Fiedor <xfiedo01@stud.fit.vutbr.cz>
 *
 *  Description:
 *    Implementation of a new state set
 *
 *****************************************************************************/

#ifndef _NEWSTATESET_HH_
#define _NEWSTATESET_HH_

#include <list>
#include <set>
#include <unordered_map>
#include <vector>

using StateType = size_t;
using SetOfStates = std::set<StateType>;
using NewStateSetList = std::list<StateType>;

class NewStateSet
{
private:  // data members

	static std::unordered_map<SetOfStates, StateType> setMap_;
	static std::vector<SetOfStates> setTable_;
	static size_t setCnt_;

public:   // methods

	static StateType GetUniqueSetHandle(const SetOfStates& state);
	static const SetOfStates& GetSetForHandle(StateType handle);
	static void DumpSetOfStates(std::ostream& os, const SetOfStates& states, size_t levelOfElements);
	static void DumpHandle(std::ostream& os, StateType state, size_t levelOfElements);
};

#endif /* _NEWSTATESET_HH_ */
