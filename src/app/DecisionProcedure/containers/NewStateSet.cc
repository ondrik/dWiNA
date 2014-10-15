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

#include <algorithm>
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


bool NewStateSet::IsSubsumedBy(
	StateType      lhs,
	StateType      rhs,
	size_t         level)
{
	const SetOfStates& lhsSet = NewStateSet::GetSetForHandle(lhs);
	const SetOfStates& rhsSet = NewStateSet::GetSetForHandle(rhs);

	return std::includes(
		rhsSet.cbegin(), rhsSet.cend(),
		lhsSet.cbegin(), lhsSet.cend());
}


bool NewStateSet::AddStateToSet(
	SetOfStates&    stateSet,
	StateType       newState,
	size_t          level)
{
	std::cerr << "[AddStateToSet] level = " << level << "\n";
	auto it = stateSet.begin();
	while (it != stateSet.end())
	{
		StateType state = *it;
		if (NewStateSet::IsSubsumedBy(newState, state, level))
		{	// if 'newState' adds nothing new
			return false;
		}
		else if (NewStateSet::IsSubsumedBy(state, newState, level))
		{	// if 'newState' is bigger than 'state', we remove 'state'
			auto newIt = it;
			++it;
			stateSet.erase(newIt);
		}
		else
		{
			++it;
		}
	}

	stateSet.insert(newState);
	return true;
}
