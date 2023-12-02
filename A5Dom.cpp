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

	// This method implements what the pass does
	void processFunction(Function &F)
	{
		std::map<BasicBlock *, std::set<BasicBlock *>> dominators;
		std::set<BasicBlock *> allBlocks;

		// First, collect all basic blocks
		for (BasicBlock &BB : F)
		{
			allBlocks.insert(&BB);
		}

		// Initialize dominators: Entry block dominates itself; all others dominate all blocks
		for (BasicBlock &BB : F)
		{
			if (&BB == &F.getEntryBlock())
			{
				// Entry block dominates itself
				dominators[&BB].insert(&BB);
			}
			else
			{
				// Assume every block dominates this block to start
				dominators[&BB] = allBlocks;
			}
		}

		// Iteratively compute dominators
		bool changed = true;
		while (changed)
		{
			changed = false;
			for (BasicBlock &BB : F)
			{
				if (&BB == &F.getEntryBlock())
					continue;

				std::set<BasicBlock *> intersectionSet = allBlocks;

				// Compute the intersection of dominators of all predecessors
				for (auto *Pred : predecessors(&BB))
				{
					std::set<BasicBlock *> tempSet;
					std::set_intersection(intersectionSet.begin(), intersectionSet.end(),
										  dominators[Pred].begin(), dominators[Pred].end(),
										  std::inserter(tempSet, tempSet.begin()));
					intersectionSet = tempSet;
				}

				// Add the current block to the intersection set
				intersectionSet.insert(&BB);

				// Update dominator set for the block if it has changed
				if (dominators[&BB] != intersectionSet)
				{
					dominators[&BB] = intersectionSet;
					changed = true;
				}
			}
		}

		// Print the dominators for each block
		for (auto &DomPair : dominators)
		{
			BasicBlock *BB = DomPair.first;
			std::set<BasicBlock *> &DomSet = DomPair.second;

			// Print the name of the basic block and its dominators
			errs() << BB->getName() << " is dominated by:\n";
			for (BasicBlock *Dom : DomSet)
			{
				errs() << "\t" << Dom->getName() << "\n";
			}
			errs() << "\n";
		}
	}
	// void processFunction(Function &F){
	// 	std::map<BasicBlock*, set<BasicBlock*>> dominators;
	// 	std::map<BasicBlock*, set<BasicBlock*>> postDominators;

	// 	std::set<BasicBlock*> allBlocks;

	// 	// First collect all basic blocks
	// 	for (BasicBlock &BB : F) {
	// 		allBlocks.insert(&BB);
	// 	}

	// 	// ECE467 STUDENT: add your code here
	// 	for (BasicBlock &BB : F){
	// 		if (&BB == &F.getEntryBlock()) {
	//         	// Entry block dominates itself
	//         	dominators[&BB] = {&BB};
	// 		} else {
	// 			// Assume every block dominates this block to start
	// 			dominators[&BB] = allBlocks;
	// 		}
	// 	}

	// 	for (auto &DomPair : dominators) {
	// 		BasicBlock *BB = DomPair.first;
	// 		std::set<BasicBlock*> &DomSet = DomPair.second;

	// 		// Print the name of the basic block
	// 		errs() << BB->getName() << " initial set of dominators:\n";

	// 		// Print the dominators
	// 		for (BasicBlock *Dom : DomSet) {
	// 			errs() << "\t" << Dom->getName() << "\n";
	// 		}
	// 		errs() << "\n";
	// 	}

	// }

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
