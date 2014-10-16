/*****************************************************************************
 *  dWiNA - Deciding WSkS using non-deterministic automata
 *
 *  Copyright (c) 2014  Tomas Fiedor <xfiedo01@stud.fit.vutbr.cz>
 *
 *  Description:
 *    WSkS Decision Procedure
 *
 *****************************************************************************/

#ifndef __DEC_PROC__H__
#define __DEC_PROC__H__

// VATA headers
#include <vata/bdd_bu_tree_aut.hh>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/binary_relation.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/convert.hh>

// MONA headers
#include "../Frontend/ast.h"
#include "../Frontend/ident.h"
#include "../Frontend/env.h"

#include <deque>
#include <memory>
#include <unordered_map>

#include "mtbdd/ondriks_mtbdd.hh"
#include "containers/VarToTrackMap.hh"
#include "containers/StateSet.hh"
#include "containers/NewStateSet.hh"
#include "containers/Cache.hh"
#include "automata.hh"
#include "mtbdd_factors.hh"

//#define PRUNE_BY_RELATION
#define SMART_FLATTEN
#define USE_STATECACHE
// BDD Cache is temporary disable due to the memory leaks
//#define USE_BDDCACHE
#define SMART_BINARY

extern VarToTrackMap varMap;
extern Options options;

// < Module Typedefs >
typedef std::vector<unsigned int> VariableSet;
typedef std::deque<VariableSet> PrefixListType;

using Automaton = VATA::BDDBottomUpTreeAut;
using StateType = size_t;
using StateHT = std::unordered_set<StateType>;
using StateTuple = std::vector<StateType>;
using MTBDDLeafStateSet = VATA::Util::OrdVector<StateType>;
using TransMTBDD = VATA::MTBDDPkg::OndriksMTBDD<MTBDDLeafStateSet>;
using MacroTransMTBDD = VATA::MTBDDPkg::OndriksMTBDD<MacroStateSet*>;
using MacroTransMTBDDNew = VATA::MTBDDPkg::OndriksMTBDD<StateType>;
typedef StateHT BaseFinalStatesType;
typedef MacroStateSet* FinalStateType;
typedef StateHT StateSetType;

// < Module Functions >
int decideWS1S(Automaton & aut, PrefixListType formulaPrefixSet, PrefixListType negFormulaPrefixSet);
int decideWS2S(Automaton & aut);
bool existsSatisfyingExample(Automaton & aut, MacroStateSet* initialState, PrefixListType formulaPrefixSet);
bool existsUnsatisfyingExample(Automaton & aut, MacroStateSet* initialState, PrefixListType negFormulaPrefixSet);
PrefixListType convertPrefixFormulaToList(ASTForm* formula);
void closePrefix(PrefixListType & prefix, IdentList* freeVars, bool negationIsTopmonst);
BaseFinalStatesType getBaseFinalStates(Automaton & aut);
const TransMTBDD* getMTBDDForStateTuple(const Automaton& aut, const StateTuple& states);
void getInitialStatesOfAutomaton(const Automaton& aut, MTBDDLeafStateSet &);
MacroStateSet* constructInitialState(Automaton &  aut, unsigned numberOfDeterminizations);
bool StateIsFinal(Automaton & aut, TStateSet* state, unsigned level, PrefixListType & prefix);
StateType GetZeroPost(Automaton & aut, StateType state, unsigned level, PrefixListType & prefix);
StateType GetZeroMacroPost(Automaton & aut, StateType state, unsigned level, PrefixListType & prefix);
int getProjectionVariable(unsigned level, const PrefixListType& prefix);
MacroTransMTBDD GetMTBDDForPost(Automaton & aut, StateType state, unsigned level, PrefixListType & prefix);
bool isNotEnqueued(StateSetList & queue, StateType state, unsigned level);

// < Backward decision procedure functions >
int decideWS1S_backwards(Automaton &aut, PrefixListType formulaPrefixSet, PrefixListType negFormulaPrefixSet, bool formulaIsGround, bool topmostIsNegation);
bool testValidity(const Automaton& aut, const PrefixListType& prefix, bool topmostIsNegation);
// StateType computeFinalStates(Automaton &aut, PrefixListType prefix, unsigned int detNo);
bool initialStateIsInFinalStates(StateType initial, StateType finalStates, unsigned int level);

#endif
