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

#define USE_SUBSUMPTION

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
	assert(level > 0);

#ifdef USE_SUBSUMPTION
	const SetOfStates& lhsSet = NewStateSet::GetSetForHandle(lhs);
	const SetOfStates& rhsSet = NewStateSet::GetSetForHandle(rhs);

	// std::cerr << "[IsSubsumedBy] testing whether ";
	// NewStateSet::DumpSetOfStates(std::cerr, lhsSet, level);
	// std::cerr << " is subsumed by ";
	// NewStateSet::DumpSetOfStates(std::cerr, rhsSet, level);
	// std::cerr << " on level " << level << "\n";

	if (lhs == rhs)
	{
		return true;
	}

	if (level == 1)
	{	// for basic sets
		return std::includes(
			lhsSet.cbegin(), lhsSet.cend(),
			rhsSet.cbegin(), rhsSet.cend());
	}

	if (level % 2 == 0)
	{
		for (StateType lhsState : lhsSet)
		{
			bool found;
			for (StateType rhsState : rhsSet)
			{
				if (NewStateSet::IsSubsumedBy(lhsState, rhsState, level-1))
				{
					found = true;
					break;
				}
			}
			if (!found)
			{
				return false;
			}
		}
		return true;
	}
	else
	{
		for (StateType rhsState : rhsSet)
		{
			bool found;
			for (StateType lhsState : lhsSet)
			{
				if (NewStateSet::IsSubsumedBy(lhsState, rhsState, level-1))
				{
					found = true;
					break;
				}
			}
			if (!found)
			{
				return false;
			}
		}
		return true;
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
	assert(level > 0);

	// std::cerr << "[AddStateToSet] level = " << level << "\n";
	// std::cerr << "[AddStateToSet] set = ";
	// NewStateSet::DumpSetOfStates(std::cerr, stateSet, level);
	// std::cerr << "\n";
	// std::cerr << "[AddStateToSet] newState = " << newState << "\n";

	if (1 == level)
	{
		return stateSet.insert(newState).second;
	}

	auto it = stateSet.begin();
	while (it != stateSet.end())
	{
		StateType state = *it;
		if (NewStateSet::IsSubsumedBy(newState, state, level-1))
		{	// if 'newState' adds nothing new
			return false;
		}
		else if (NewStateSet::IsSubsumedBy(state, newState, level-1))
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

	if (!stateSet.insert(newState).second)
	{
		assert(false);
	}

	return true;
}
