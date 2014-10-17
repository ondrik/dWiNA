/*****************************************************************************
 *  VATA Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    My own implementation of multi-terminal binary decision diagrams (MTBDDs)
 *
 *****************************************************************************/

#ifndef _VATA_ONDRIKS_MTBDD_HH_
#define _VATA_ONDRIKS_MTBDD_HH_

// VATA headers
#include	<vata/vata.hh>
#include	<vata/sym_var_asgn.hh>
#include	<vata/util/triple.hh>
#include  <vata/notimpl_except.hh>

#include	"mtbdd_node.hh"

// Standard library headers
#include	<cassert>
#include	<stdint.h>
#include	<stdexcept>
#include	<vector>
#include  <memory>
#include  <unordered_map>

// Boost library headers
#include <boost/functional/hash.hpp>

namespace VATA
{
	namespace MTBDDPkg
	{
		template <
			typename Data
		>
		class OndriksMTBDD;

		template <class, typename, typename>
		class Apply1Functor;

		template <class, typename, typename, typename>
		class Apply2Functor;

		template <class, typename, typename, typename>
		class PersCacheApply2Functor;

		template <class, typename, typename, typename, typename>
		class Apply3Functor;

		template <class, typename>
		class VoidApply1Functor;

		template <class, typename, typename>
		class VoidApply2Functor;

		template <class, typename, typename, typename>
		class VoidApply3Functor;
	}
}


/**
 * @brief   Class representing MTBDD
 *
 * This class represents a single multi-terminal binary decision diagram
 * (MTBDD).
 *
 * @tparam  Data  The type of leaves
 */
template <
	typename Data
>
class VATA::MTBDDPkg::OndriksMTBDD
{
	template <class, typename, typename>
	friend class Apply1Functor;

	template <class, typename, typename, typename>
	friend class Apply2Functor;

	template <class, typename, typename, typename>
	friend class PersCacheApply2Functor;

	template <class, typename, typename, typename, typename>
	friend class Apply3Functor;

	template <class, typename>
	friend class VoidApply1Functor;

	template <class, typename, typename>
	friend class VoidApply2Functor;

	template <class, typename, typename, typename>
	friend class VoidApply3Functor;

public:   // public data types

	typedef Data DataType;

private:  // private data types

	typedef MTBDDNodePtr<DataType> NodePtrType;

public:   // public data types

	typedef typename NodePtrType::VarType VarType;
	typedef std::vector<VarType> PermutationTable;
	typedef std::shared_ptr<PermutationTable> PermutationTablePtr;

private:  // private data types

	typedef VATA::Util::Triple<NodePtrType, NodePtrType, VarType>
		InternalAddressType;

	typedef std::unordered_map<InternalAddressType, NodePtrType,
		boost::hash<InternalAddressType>> InternalCacheType;

	typedef std::unordered_map<DataType, NodePtrType,
		boost::hash<DataType>> LeafCacheType;

	typedef VATA::Util::Convert Convert;

	typedef std::unordered_set<NodePtrType, boost::hash<NodePtrType>> NodePtrSet;

private:  // private data members

	NodePtrType root_;

	DataType defaultValue_;

	static LeafCacheType leafCache_;
	static InternalCacheType internalCache_;


private:  // private methods


	/**
	 * @brief  Function for constructing an MTBDD
	 *
	 * This function is used for constructing a new MTBDD, such that the
	 * variable assignment @p asgn is set to @p value and all other assignments
	 * are set to @p defaultValue.
	 *
	 * @param  asgn          Variable assignment to be set to @p value
	 * @param  value         Value to be set for assignment @p asgn
	 * @param  defaultValue  Value to be set for all assignments other than @p
	 *                       asgn
	 *
	 * @return  The constructed MTBDD
	 */
	static NodePtrType constructMTBDD(
		const SymbolicVarAsgn&      asgn,
		const DataType&             value,
		const DataType&             defaultValue)
	{
		return constructMTBDD(asgn, spawnLeaf(value), defaultValue,
			[](const VarType& var){return var;});
	}

	template <class VariableTranslation>
	static NodePtrType constructMTBDD(
		const SymbolicVarAsgn&            asgn,
		NodePtrType                       node,
		const DataType&                   defaultValue,
		VariableTranslation               varTrans)
	{
		if (IsLeaf(node) && (GetDataFromLeaf(node) == defaultValue))
		{	// in case an MTBDD with a single leaf is processed
			IncrementRefCnt(node);
			return node;
		}

		// the sink leaf
		NodePtrType sink = spawnLeaf(defaultValue);

		// working node
		NodePtrType procNode = node;

		for (size_t i = 0; i < asgn.length(); ++i)
		{	// construct the MTBDD according to the variable ordering
			VarType var =	i;
			if (asgn.GetIthVariableValue(var) == SymbolicVarAsgn::ONE)
			{	// in case the variable is 1
				procNode = spawnInternal(sink, procNode, varTrans(var));
			}
			else if (asgn.GetIthVariableValue(var) == SymbolicVarAsgn::ZERO)
			{	// in case the variable is 0
				procNode = spawnInternal(procNode, sink, varTrans(var));
			}
			// otherwise don't care about the variable
		}

		if (procNode == node)
		{	// in case there is nothing above the original node
			if (GetLeafRefCnt(sink) == 0)
			{	// in case there is no one pointing to the sink
				disposeOfLeafNode(sink);
			}
		}

		IncrementRefCnt(procNode);
		return procNode;
	}

	OndriksMTBDD(
		NodePtrType                   root,
		const DataType&               defaultValue) :
		root_(root),
		defaultValue_(defaultValue)
	{
		// Assertions
		assert(!IsNull(root_));
	}


	NodePtrType getRoot() const
	{
		return root_;
	}

	static void disposeOfLeafNode(NodePtrType node)
	{
		// Assertions
		assert(!IsNull(node));
		assert(IsLeaf(node));

		if (leafCache_.erase(GetDataFromLeaf(node)) != 1)
		{	// in case the leaf was not cached
			assert(false);     // fail gracefully
		}

		DeleteLeafNode(node);
	}

	static void disposeOfInternalNode(NodePtrType node)
	{
		// Assertions
		assert(!IsNull(node));
		assert(IsInternal(node));

		InternalAddressType addr(GetLowFromInternal(node),
			GetHighFromInternal(node), GetVarFromInternal(node));
		if (internalCache_.erase(addr) != 1)
		{	// in case the internal was not cached
			assert(false);   // fail gracefully
		}

		recursivelyDeleteMTBDDNode(GetLowFromInternal(node));
		recursivelyDeleteMTBDDNode(GetHighFromInternal(node));

		DeleteInternalNode(node);
	}

	static void recursivelyDeleteMTBDDNode(NodePtrType node)
	{
		// Assertions
		assert(!IsNull(node));

		if (IsLeaf(node))
		{	// for leaves
			if (DecrementLeafRefCnt(node) == 0)
			{	// this reference to node is the last
				disposeOfLeafNode(node);
			}
		}
		else
		{	// for internal nodes
			assert(IsInternal(node));

			if (DecrementInternalRefCnt(node) == 0)
			{	// this reference to node is the last
				// disposeOfInternalNode(node);
			}
		}
	}

	inline void deleteMTBDD()
	{
		if (!IsNull(root_))
		{
			recursivelyDeleteMTBDDNode(root_);
			root_ = 0;
		}
	}

	// TODO: optimize
	static inline NodePtrType spawnLeaf(const DataType& data)
	{
		NodePtrType result = 0;

		typename LeafCacheType::const_iterator itLC;
		if ((itLC = leafCache_.find(data)) != leafCache_.end())
		{	// in case given leaf is already cached
			result = itLC->second;
		}
		else
		{	// if the leaf doesn't exist
			result = CreateLeaf(data);
			leafCache_.insert(std::make_pair(data, result));
		}

		assert(!IsNull(result));
		return result;
	}

	// TODO: optimize
	static inline NodePtrType spawnInternal(
		NodePtrType low, NodePtrType high, const VarType& var)
	{
		NodePtrType result = 0;

		InternalAddressType addr(low, high, var);
		typename InternalCacheType::const_iterator itIC;
		if ((itIC = internalCache_.find(addr)) != internalCache_.end())
		{	// in case given internal is already cached
			result = itIC->second;
		}
		else
		{	// if the internal doesn't exist
			result = CreateInternal(low, high, var);
			IncrementRefCnt(low);
			IncrementRefCnt(high);
			internalCache_.insert(std::make_pair(addr, result));
		}

		assert(!IsNull(result));
		return result;
	}

	static std::string mtbddNodeToDotString(const NodePtrType& ptr, NodePtrSet& cache)
	{
		// Assertions
		assert(!IsNull(ptr));

		if (cache.find(ptr) != cache.end())
		{
			return "";
		}

		cache.insert(ptr);

		if (IsLeaf(ptr))
		{
			DataType data = GetDataFromLeaf(ptr);
			return Convert::ToString(ptr) + " [label = \"" +
				Convert::ToString(data) + "\"]" + "\n";
		}
		else
		{
			assert(IsInternal(ptr));

			return "var(" + Convert::ToString(GetVarFromInternal(ptr)) + ")" + Convert::ToString(ptr) + " -> " +
				Convert::ToString(GetLowFromInternal(ptr)) + " [style = dashed];\n" +
				"var(" + Convert::ToString(GetVarFromInternal(ptr)) + ")" + Convert::ToString(ptr) + " -> " +
				Convert::ToString(GetHighFromInternal(ptr)) + " [style = solid];\n" +
				mtbddNodeToDotString(GetLowFromInternal(ptr), cache) +
				mtbddNodeToDotString(GetHighFromInternal(ptr), cache);
		}
	}

	template <
		class VarPredicate,
		class ApplyFunc>
	static NodePtrType projectNode(
		const NodePtrType             node,
		VarPredicate                  pred,
		ApplyFunc&                    applyFunc,
		const DataType&               defaultValue)
	{
		assert(!IsNull(node));

		if (IsLeaf(node))
		{
			return OndriksMTBDD::spawnLeaf(GetDataFromLeaf(node));
		}

		VarType var = GetVarFromInternal(node);
		NodePtrType lowTree = GetLowFromInternal(node);
		NodePtrType highTree = GetHighFromInternal(node);

		assert(lowTree != highTree);
		assert(node != lowTree);
		assert(node != highTree);

		lowTree = projectNode(lowTree, pred, applyFunc, defaultValue);
		highTree = projectNode(highTree, pred, applyFunc, defaultValue);
		assert(!IsNull(lowTree) && !IsNull(highTree));

		NodePtrType result(reinterpret_cast<const uintptr_t>(nullptr));
		if (pred(var))
		{	// if the node is to be removed
			result = applyFunc(lowTree, highTree);
		}
		else if (lowTree == highTree)
		{
			result = lowTree;
		}
		else
		{
			result = OndriksMTBDD::spawnInternal(lowTree, highTree, var);
		}

		assert(!IsNull(result));

		if (IsInternal(result))
		{	// check some invariants
			lowTree = GetLowFromInternal(result);
			highTree = GetHighFromInternal(result);

			assert(result != lowTree);
			assert(result != highTree);
			assert(lowTree != highTree);
		}

		return result;
	}


public:   // public methods


	/**
	 * @brief  Constructor with given variable ordering
	 *
	 * This constructor creates a new MTBDD , such that the variable assignment
	 * @p asgn is set to @p value and all other assignments are set to @p
	 * defaultValue.
	 *
	 * @param  asgn          Variable assignment to be set to @p value
	 * @param  value         Value to be set for assignment @p asgn
	 * @param  defaultValue  Value to be set for all assignments other than @p
	 *                       asgn
	 */
	OndriksMTBDD(
		const SymbolicVarAsgn&            asgn,
		const DataType&                   value,
		const DataType&                   defaultValue) :
		root_(static_cast<uintptr_t>(0)),
		defaultValue_(defaultValue)
	{
		// create the MTBDD
		root_ = constructMTBDD(asgn, value, defaultValue_);
	}

	OndriksMTBDD(const OndriksMTBDD& mtbdd)
		: root_(mtbdd.root_),
			defaultValue_(mtbdd.defaultValue_)
	{
		// Assertions
		assert(!IsNull(root_));

		IncrementRefCnt(root_);
	}

	explicit OndriksMTBDD(const DataType& value)
		: root_(spawnLeaf(value)),
			defaultValue_(value)
	{
		// Assertions
		assert(!IsNull(root_));

		// TODO: do something about variable ordering

		IncrementRefCnt(root_);
	}

	OndriksMTBDD& operator=(const OndriksMTBDD& mtbdd)
	{
		// Assertions
		assert(!IsNull(root_));

		if (&mtbdd == this)
			return *this;

		deleteMTBDD();

		root_ = mtbdd.root_;
		IncrementRefCnt(root_);

		defaultValue_ = mtbdd.defaultValue_;

		return *this;
	}

	const DataType& GetDefaultValue() const
	{
		return defaultValue_;
	}

	OndriksMTBDD ExtendWith(
		const SymbolicVarAsgn&         asgn,
		const size_t&                  offset) const
	{
		return OndriksMTBDD(constructMTBDD(asgn, root_, GetDefaultValue(),
			[&offset](const VarType& var){return var + offset;}), GetDefaultValue());
	}

	/**
	 * @brief  Returns value for assignment
	 *
	 * Thsi method returns a value in the MTBDD that corresponds to given
	 * variable assignment @p asgn.
	 *
	 * @note  If there are multiple values that correspond to given variable
	 * assignment (e.g., because the assignment is very nondeterministic), an
	 * arbitrary value is returned.
	 *
	 * @param  asgn  Variable assignment
	 *
	 * @return  Value corresponding to variable assignment @p asgn
	 */
	const DataType& GetValue(
		const SymbolicVarAsgn&           asgn) const
	{
		NodePtrType node = root_;

		while (!IsLeaf(node))
		{	// try to proceed according to the assignment
			const VarType& var = GetVarFromInternal(node);

			if ((var < asgn.length()) && (asgn.GetIthVariableValue(var) == SymbolicVarAsgn::ONE))
			{	// if one
				node = GetHighFromInternal(node);
			}
			else
			{	// if zero or don't care
				node = GetLowFromInternal(node);
			}
		}

		return GetDataFromLeaf(node);
	}

	static std::string DumpToDot(
		const std::vector<const OndriksMTBDD*>&           mtbdds)
	{
		std::string result = "digraph mtbdd {\n";

		NodePtrSet cache;

		for (const OndriksMTBDD* bdd : mtbdds)
		{
			assert(bdd != nullptr);

			result +=	mtbddNodeToDotString(bdd->getRoot(), cache);
		}

		return result + "}";
	}


	/**
	 * @brief  Retrieve a sub-MTBDD for a prefix
	 *
	 * Given an assignment @p asgn and an @p offset, this method returns a
	 * sub-MTBDD that corresponds to a DAG rooted at a node that is reachable
	 * using @p asgn from the root of @p this. @p offset determines the highest
	 * number of a Boolean variable that will be in the resulting MTBDD (so it
	 * cuts of all Boolean variables with higher numbers than this).
	 *
	 * @note  There may be more than one MTBDD corresponding to a prefix; the
	 *        lowest one (accessible via '0's) is returned in such a case
	 *
	 * @param[in]  asgn      The prefix
	 * @param[in]  offset    The number of Boolean variables to keep
	 *
	 * @returns  An MTBDD under the prefix given by @p asgn
	 */
	OndriksMTBDD GetMtbddForPrefix(
		const SymbolicVarAsgn&           asgn,
		const size_t&                    offset) const
	{
		NodePtrType newRoot = root_;

		while (!IsLeaf(newRoot))
		{
			const VarType& var = GetVarFromInternal(newRoot);
			if (var < offset)
			{
				break;
			}

			if (asgn.GetIthVariableValue(var - offset) == SymbolicVarAsgn::ONE)
			{	// if one
				newRoot = GetHighFromInternal(newRoot);
			}
			else
			{	// if zero or don't care
				newRoot = GetLowFromInternal(newRoot);
			}
		}

		IncrementRefCnt(newRoot);
		return OndriksMTBDD(newRoot, defaultValue_);
	}


	/**
	 * @brief  Project out variables specified by a predicate
	 *
	 * This method returns an MTBDD with removed nodes that satisfy the @p pred
	 * predicate. If such a node is encounted in a traversal of the MTBDD, its
	 * children are combined using a binary apply operation that performs the @p
	 * leafFunc function on the leaves.
	 *
	 * @param[in]  pred       The predicate that denotes the nodes to be removed
	 * @param[in]  applyFunc  The apply functor to apply on children of a node
	 *                        projected out
	 *
	 * @returns  An MTBDD that corresponds to the projection given by the input
	 *           parameters
	 */
	template <
		class VarPredicate,
		class ApplyFunc>
	OndriksMTBDD Project(
		VarPredicate             pred,
		ApplyFunc&               applyFunc) const
	{
		assert(!IsNull(this->getRoot()));

		NodePtrType newRoot = OndriksMTBDD::projectNode(
			this->getRoot(), pred, applyFunc, this->GetDefaultValue());
		IncrementRefCnt(newRoot);
		return OndriksMTBDD(newRoot, this->GetDefaultValue());
	}


	/**
	 * @brief  Rename variables
	 *
	 * This method renames the variables of the MTBDD according to the renaming
	 * functor given in @p renamer.
	 *
	 * @param[in,out]  renamer  A functor that renames the variables
	 *
	 * @returns  An MTBDD with renamed variables
	 *
	 * @note  The @p renamer must respect the ordering of variables. That is, for
	 *        all x, y, if x < y, then it must hold that renamer(x) < renamer(y)
	 */
	template <
		class RenamingF>
	OndriksMTBDD Rename(
		RenamingF                renamer) const
	{
		throw NotImplementedException(__func__);
	}


	~OndriksMTBDD()
	{
		deleteMTBDD();
	}
};

template <typename Data>
typename VATA::MTBDDPkg::OndriksMTBDD<Data>::LeafCacheType
	VATA::MTBDDPkg::OndriksMTBDD<Data>::leafCache_;

template <typename Data>
typename VATA::MTBDDPkg::OndriksMTBDD<Data>::InternalCacheType
	VATA::MTBDDPkg::OndriksMTBDD<Data>::internalCache_;

#endif
