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

// #define SUBSUMPTION

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
	size_t level)
{
	if (0 == level)
	{
		os << state;
	}
	else
	{
		os << state << "=";
		NewStateSet::DumpSetOfStates(os, NewStateSet::GetSetForHandle(state), level);
	}
}

void NewStateSet::DumpSetOfStates(
	std::ostream&          os,
	const SetOfStates&     states,
	size_t                 level)
{
	assert(level > 0);

	os << "{";
	for (auto it = states.cbegin(); it != states.cend(); ++it)
	{
		if (states.cbegin() != it)
		{
			os << ", ";
		}

		NewStateSet::DumpHandle(os, *it, level-1);
	}
	os << "}";
}


bool NewStateSet::IsSubsumedBy(
	StateType      lhs,
	StateType      rhs,
	size_t         level)
{
#ifdef SUBSUMPTION
	const SetOfStates& lhsSet = NewStateSet::GetSetForHandle(lhs);
	const SetOfStates& rhsSet = NewStateSet::GetSetForHandle(rhs);

	if (level % 2 == 0)
	{
		return std::includes(
			rhsSet.cbegin(), rhsSet.cend(),
			lhsSet.cbegin(), lhsSet.cend());
	}
	else
	{
		return std::includes(
			lhsSet.cbegin(), lhsSet.cend(),
			rhsSet.cbegin(), rhsSet.cend());
	}
#else
	return lhs == rhs;
#endif
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
