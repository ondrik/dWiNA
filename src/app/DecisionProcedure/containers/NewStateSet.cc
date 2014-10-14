/*****************************************************************************
 *  dWiNA - Deciding WSkS using non-deterministic automata
 *
 *  Copyright (c) 2014  Tomas Fiedor <xfiedo01@stud.fit.vutbr.cz>
 *
 *  Description:
 *    Implementation of a new state set
 *
 *****************************************************************************/

#include "NewStateSet.hh"

#include <boost/functional/hash.hpp>

namespace std
{
	template <>
	struct hash<SetOfStates>
	{
		std::size_t operator()(const SetOfStates& k) const
		{
			return boost::hash_value(k);
		}
	};
}

// global guys
std::unordered_map<SetOfStates, StateType> NewStateSet::setMap_;
std::vector<SetOfStates> NewStateSet::setTable_;
size_t NewStateSet::setCnt_ = 0;


StateType NewStateSet::GetUniqueSetHandle(const SetOfStates& state)
{
	auto iteratorBoolPair = NewStateSet::setMap_.insert(std::make_pair(state, 0));
	if (iteratorBoolPair.second)
	{	// if we inserted
		iteratorBoolPair.first->second = NewStateSet::setCnt_++;
		NewStateSet::setTable_.push_back(state);
	}

	return iteratorBoolPair.first->second;
}

const SetOfStates& NewStateSet::GetSetForHandle(StateType handle)
{
	assert(handle < NewStateSet::setCnt_);
	return setTable_[handle];
}


void NewStateSet::DumpHandle(
	std::ostream& os,
	StateType state,
	size_t levelOfElements)
{
	if (0 == levelOfElements)
	{
		os << state;
	}
	else
	{
		NewStateSet::DumpSetOfStates(os, NewStateSet::GetSetForHandle(state), levelOfElements-1);
	}
}

void NewStateSet::DumpSetOfStates(
	std::ostream& os,
	const SetOfStates& states,
	size_t levelOfElements)
{
	os << "{";
	for (auto it = states.cbegin(); it != states.cend(); ++it)
	{
		if (states.cbegin() != it)
		{
			os << ", ";
		}

		NewStateSet::DumpHandle(os, *it, levelOfElements);
	}
	os << "}";
}
