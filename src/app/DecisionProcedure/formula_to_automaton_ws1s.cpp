#include "../Frontend/ast.h"
#include "../Frontend/symboltable.h"

#include <cstring>

// VATA headers
#include <vata/bdd_bu_tree_aut.hh>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/binary_relation.hh>

#include "automata.hh"

using std::cout;

extern SymbolTable symbolTable;

using Automaton = VATA::BDDBottomUpTreeAut;

/**
 * Constructs automaton for unary automaton True
 *
 * @param[out] trueAutomaton: created automaton
 * @param doComplement: whether automaton should be complemented
 * TODO: do Complement
 */
void ASTForm_True::toUnaryAutomaton(Automaton &trueAutomaton, bool doComplement) {
    // (X^k) -> q0
	addUniversalTransition(trueAutomaton, Automaton::StateTuple(), 0);

    // q0 -(X^k)-> q0
	addUniversalTransition(trueAutomaton, Automaton::StateTuple({0}), 0);

    // Final state q0
	setFinalState(trueAutomaton, doComplement, 0);
}

/**
 * Constructs automaton for unary automaton False
 *
 * @param[out] falseAutomaton: created automaton
 * @param doComplement: whether automaton should be complemented
 * TODO: do Complement
 */
void ASTForm_False::toUnaryAutomaton(Automaton &falseAutomaton, bool doComplement) {
	// (X^k) -> q0
	addUniversalTransition(falseAutomaton, Automaton::StateTuple(), 0);

	// q0 -(X^k)-> q0
	addUniversalTransition(falseAutomaton, Automaton::StateTuple({0}), 0);

	// no final states
	setNonFinalState(falseAutomaton, doComplement, 0);
}

/**
 * Constructs automaton for formula not phi
 *
 * Does complementation of states. Since negations should be thanks to
 * formula being conversed to exPNF form, so determinization does not need
 * to take place
 *
 * @param[out] notAutomaton: created automaton
 * @param doComplement: whether automaton should be complemented
 */
void ASTForm_Not::toUnaryAutomaton(Automaton &notAutomaton, bool doComplement) {
	// Inner formula is first conversed to unary automaton
	this->f->toUnaryAutomaton(notAutomaton, true);
}

/**
 * Constructs automaton for formula phi and psi
 *
 * First converts formulae phi and psi to automatons and then does a automata
 * product to compute the final automaton.
 *
 * @param[out] andAutomaton: created automaton
 * @param doComplement: whether automaton should be complemented
 */
void ASTForm_And::toUnaryAutomaton(Automaton &andAutomaton, bool doComplement) {
	// Inner formulas are first conversed to unary automatons
	Automaton left, right;
	this->f1->toUnaryAutomaton(left, doComplement);
	this->f2->toUnaryAutomaton(right, doComplement);

	andAutomaton = Automaton::Intersection(left, right);
}

/**
 * Constructs automaton for formula phi or psi
 *
 * First converts formulae phi or psi to automatons and then does a automata
 * union to compute the final automaton.
 *
 * @param[out] orAutomaton: created automaton
 * @param doComplement: whether automaton should be complemented
 */
void ASTForm_Or::toUnaryAutomaton(Automaton &orAutomaton, bool doComplement) {
	// Inner formulas are first conversed to unary automatons
	Automaton left, right;
	this->f1->toUnaryAutomaton(left, doComplement);
	this->f2->toUnaryAutomaton(right, doComplement);

	orAutomaton = Automaton::Union(left, right);
}

/**
 * Constructs automaton for atomic formula T1 = T2, according to its structure:
 *  1) X = Y1
 *  2) T1 = T2
 *  3) X = e
 *
 * TODO: Y1 = X? Switch?
 *  Constructs template automaton, that does acceptance of the formula
 *
 *  @return Automaton corresponding to the formula phi or psi
 */
void ASTForm_Equal2::toUnaryAutomaton(Automaton &aut, bool doComplement) {
	// 1) X = Y1
	if(this->T1->kind == aVar2 && this->T2->kind == aPlus2) {
		ASTTerm2_Var2* XTerm = (ASTTerm2_Var2*) this->T1;
		unsigned int X = XTerm->n;
		ASTTerm2_Var2* YTerm = (ASTTerm2_Var2*) ((ASTTerm2_Plus*) this->T2)->T;
		unsigned int Y = YTerm->n;
		// (x00x) -> q0
		addTransition(aut, Automaton::StateTuple(), X, Y, (char *) "00", 0);

		// (x10x) -> q0
		addTransition(aut, Automaton::StateTuple(), X, Y, (char *) "10", 0);

		// q0 -(x00x)-> q0
		addTransition(aut, Automaton::StateTuple({0}), X, Y, (char *) "00", 0);

		// q0 -(x10x)-> q1
		addTransition(aut, Automaton::StateTuple({0}), X, Y, (char *) "10", 1);

		// q1 -(x01x)-> q2
		addTransition(aut, Automaton::StateTuple({1}), X, Y, (char *) "01", 2);

		// q2 -(x00x)-> q2
		addTransition(aut, Automaton::StateTuple({2}), X, Y, (char *) "00", 2);

		// set q2 final
		setNonFinalState(aut, doComplement, 0);
		setNonFinalState(aut, doComplement, 1);
		setFinalState(aut, doComplement, 2);

	// 2) T1 = T2
	} else if (this->T1->kind == aVar2 && this->T2->kind == aVar2) {
		ASTTerm2_Var2* T1Term = (ASTTerm2_Var2*) this->T1;
		unsigned int T1 = T1Term->n;
		ASTTerm2_Var2* T2Term = (ASTTerm2_Var2*) this->T2;
		unsigned int T2 = T2Term->n;

		// (x00x) -> q0
		addTransition(aut, Automaton::StateTuple(), T1, T2, (char *) "00", 0);

		// (x11x) -> q0
		addTransition(aut, Automaton::StateTuple(), T1, T2, (char *) "11", 0);

		// q0 -(x00x)-> q0
		addTransition(aut, Automaton::StateTuple({0}), T1, T2, (char *) "00", 0);

		// q0 -(x11x)-> q0
		addTransition(aut, Automaton::StateTuple({0}), T1, T2, (char *) "11", 0);

		// set q0 final
		setFinalState(aut, doComplement, 0);
	// 3) X = e
	// this should be X = {0} hopefully
	} else {
		ASTTerm2_Var2 *XTerm = (ASTTerm2_Var2*) this->T1;
		unsigned int X = XTerm->n;

		// (x1x)-> q0
		addTransition(aut, Automaton::StateTuple(), X, '1', 0);

		// set q0 final
		setFinalState(aut, doComplement, 0);
	}
}

/**
 * Constructs automaton for atomic formula T1 sub T2
 *
 * @return Automaton corresponding to the formula T1 sub T2
 */
void ASTForm_Sub::toUnaryAutomaton(Automaton &aut, bool doComplement) {
	ASTTerm2_Var2* T1Var = (ASTTerm2_Var2*) this->T1;
	unsigned int T1 = (unsigned int) T1Var->n;

	ASTTerm2_Var2* T2Var = (ASTTerm2_Var2*) this->T2;
	unsigned int T2 = (unsigned int) T2Var->n;
	//  -(x00x)-> q0
	addTransition(aut, Automaton::StateTuple(), T1, T2, (char *) "00", 0);

	//  -(x11x)-> q0
	addTransition(aut, Automaton::StateTuple(), T1, T2, (char *) "11", 0);

	// -(x01x)-> q0
	addTransition(aut, Automaton::StateTuple(), T1, T2, (char *) "01", 0);

	// q0 -(x00x)-> q0
	addTransition(aut, Automaton::StateTuple({0}), T1, T2, (char *) "00", 0);

	// q0 -(x11x)-> q0
	addTransition(aut, Automaton::StateTuple({0}), T1, T2, (char *) "11", 0);

	// q0 -(x01x)-> q0
	addTransition(aut, Automaton::StateTuple({0}), T1, T2, (char *) "01", 0);

	// final state q0
	setFinalState(aut, doComplement, 0);
}

/**
 * Constructs automaton for formula denoting, that set is a singleton
 *
 * @return Automaton corresponding to the formula Singleton(X)
 */
void ASTForm_FirstOrder::toUnaryAutomaton(Automaton &aut, bool doComplement) {
	ASTTerm2_Var2 *XVar = (ASTTerm2_Var2*) this->t;
	unsigned int X = (unsigned int) XVar->n;

	// -(x0x)-> q0
	addTransition(aut, Automaton::StateTuple(), X, '0', 0);

	// -(x1x)-> q1
	addTransition(aut, Automaton::StateTuple(), X, '1', 0);

	// q0 -(x0x)-> q0
	addTransition(aut, Automaton::StateTuple({0}), X, '0', 0);

	// q0 -(x1x)-> q1
	addTransition(aut, Automaton::StateTuple({0}), X, '1', 1);

	// q1 -(x0x)-> q1
	addTransition(aut, Automaton::StateTuple({1}), X, '0', 1);

	// final state q1
	setNonFinalState(aut, doComplement, 0);
	setFinalState(aut, doComplement, 1);
}
