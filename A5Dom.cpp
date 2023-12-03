//
//  A5Dom.cpp
//  ECE467 Lab 5
//
//  Created by Tarek Abdelrahman on 2023-11-18.
//  Copyright © 2023 Tarek Abdelrahman. All rights reserved.
//
//  Permission is hereby granted to use this code in ECE467 at
//  the University of Toronto. It is prohibited to distribute
//  this code, either publicly or to third parties.
//

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <map>
#include <vector>
#include <set>
#include <iterator>
#include <algorithm>

using namespace llvm;
using namespace std;

namespace
{

	
	std::map<BasicBlock *, std::set<BasicBlock *>> computeDominators(Function &F) {
		std::map<BasicBlock *, std::set<BasicBlock *>> dominators;
		std::set<BasicBlock *> allBlocks;

		for (BasicBlock &BB : F) {
			allBlocks.insert(&BB);
		}

		for (BasicBlock &BB : F) {
			if (&BB == &F.getEntryBlock()) {
				dominators[&BB].insert(&BB);
			} else {
				dominators[&BB] = allBlocks;
			}
		}

		bool changed = true;
		while (changed) {
			changed = false;
			for (BasicBlock &BB : F) {
				if (&BB == &F.getEntryBlock())
					continue;

				std::set<BasicBlock *> intersectionSet = allBlocks;
				for (auto *Pred : predecessors(&BB)) {
					std::set<BasicBlock *> tempSet;
					std::set_intersection(intersectionSet.begin(), intersectionSet.end(),
										dominators[Pred].begin(), dominators[Pred].end(),
										std::inserter(tempSet, tempSet.begin()));
					intersectionSet = tempSet;
				}

				intersectionSet.insert(&BB);
				if (dominators[&BB] != intersectionSet) {
					dominators[&BB] = intersectionSet;
					changed = true;
				}
			}
		}

		return dominators;
	}

	// Function to compute dominated blocks
	std::map<BasicBlock *, std::set<BasicBlock *>> computeDominatedBlocks(Function &F, std::map<BasicBlock *, std::set<BasicBlock *>> &dominators) {
		std::map<BasicBlock *, std::set<BasicBlock *>> dominatedBlocks;
		for (BasicBlock &BB : F) {
			dominatedBlocks[&BB] = std::set<BasicBlock *>();
		}

		for (BasicBlock &BB : F) {
			dominatedBlocks[&BB].insert(&BB);
			for (BasicBlock &OtherBB : F) {
				if (&BB != &OtherBB && dominators[&OtherBB].find(&BB) != dominators[&OtherBB].end()) {
					dominatedBlocks[&BB].insert(&OtherBB);
				}
			}
		}

		return dominatedBlocks;
	}

	// Function to compute immediate dominators
	std::map<BasicBlock *, BasicBlock *> computeImmediateDominators(Function &F, std::map<BasicBlock *, std::set<BasicBlock *>> &dominators) {
		std::map<BasicBlock *, BasicBlock *> immediateDominators;
		for (BasicBlock &BB : F) {
			if (&BB == &F.getEntryBlock())
				continue; // Skip the entry block

			std::set<BasicBlock *> DOM_d = dominators[&BB];
			DOM_d.erase(&BB);

			BasicBlock *iDom = nullptr;
			for (BasicBlock *candidateIDom : DOM_d) {
				bool dominatedByOther = false;
				for (BasicBlock *other : DOM_d) {
					if (other != candidateIDom && dominators[other].find(candidateIDom) != dominators[other].end()) {
						dominatedByOther = true;
						break;
					}
				}
				if (!dominatedByOther) {
					iDom = candidateIDom;
					break;
				}
			}

			if (iDom != nullptr) {
				immediateDominators[&BB] = iDom;
			}
		}
		return immediateDominators;
	}
	// This method implements what the pass does
	void processFunction(Function &F){
		auto dominators = computeDominators(F);
		auto dominatedBlocks = computeDominatedBlocks(F, dominators);
		auto immediateDominators = computeImmediateDominators(F, dominators);

		// Print out the dominated blocks
		for (auto &DominatedPair : dominatedBlocks) {
			BasicBlock *BB = DominatedPair.first;
			std::set<BasicBlock *> &DominatedSet = DominatedPair.second;

			errs() << BB->getName() << " dominates:\n";
			for (BasicBlock *DominatedBB : DominatedSet) {
				errs() << "\t" << DominatedBB->getName() << "\n";
			}
			errs() << "\n";
		}

		// Print out the immediate dominators
		for (BasicBlock &BB : F) {
			if (&BB != &F.getEntryBlock()) { // Skip the entry block
				BasicBlock *iDom = immediateDominators[&BB];
				errs() << BB.getName() << "'s immediate dominator is " << (iDom ? iDom->getName() : "null") << "\n";
			}
		}
	}

	struct A5Dom : PassInfoMixin<A5Dom>
	{
		// This is the main entry point for processing the IR of a function
		// It simply calls the function that has your code
		PreservedAnalyses run(Function &F, FunctionAnalysisManager &)
		{
			processFunction(F);
			return PreservedAnalyses::all();
		}

		// This makes sure that the pass is executed, even when functions are
		// decorated with the optnone attribute; this is the case when using
		// clang without -O flags
		static bool isRequired() { return true; }
	};
} // namespace

// Register the pass with the pass manager as a function pass
llvm::PassPluginLibraryInfo getA5DomPluginInfo()
{
	return {LLVM_PLUGIN_API_VERSION, "A5Dom", LLVM_VERSION_STRING,
			[](PassBuilder &PB)
			{
				PB.registerPipelineParsingCallback(
					[](StringRef Name, FunctionPassManager &FPM,
					   ArrayRef<PassBuilder::PipelineElement>)
					{
						if (Name == "A5Dom")
						{
							FPM.addPass(A5Dom());
							return true;
						}
						return false;
					});
			}};
}

// This ensures that opt recognizes A5Dom when specified on the
// command line by -passes="A5Dom"
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo()
{
	return getA5DomPluginInfo();
}
