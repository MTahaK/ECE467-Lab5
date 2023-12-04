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
	std::map<BasicBlock *, std::set<BasicBlock *>> reverseCFG(Function &F) {
		std::map<BasicBlock *, std::set<BasicBlock *>> reversedCFG;

		// Initialize the map with empty sets for all blocks
		for (BasicBlock &BB : F) {
			reversedCFG[&BB] = std::set<BasicBlock *>();
		}

		// Create reversed edges by considering successors as predecessors
		for (BasicBlock &BB : F) {
			for (succ_iterator SI = succ_begin(&BB), E = succ_end(&BB); SI != E; ++SI) {
				BasicBlock *Successor = *SI;
				reversedCFG[Successor].insert(&BB);
			}
		}

		// // Optionally, create a virtual exit node and connect all exit blocks to it
		// // This is not a real basic block, just a conceptual tool for our analysis
		// BasicBlock *virtualExit = (BasicBlock *)(intptr_t)(-1); // Using -1 cast to a pointer as a placeholder for the virtual exit

		// for (BasicBlock &BB : F) {
		// 	if (isa<ReturnInst>(BB.getTerminator()) || isa<UnreachableInst>(BB.getTerminator())) {
		// 		reversedCFG[virtualExit].insert(&BB);
		// 	}
		// }
		return reversedCFG;
	}

	std::map<BasicBlock *, std::set<BasicBlock *>> createCFGMap(Function &F) {
		std::map<BasicBlock *, std::set<BasicBlock *>> CFGMap;

		for (BasicBlock &BB : F) {
			std::set<BasicBlock *> predSet;
			for (auto *Pred : predecessors(&BB)) {
				predSet.insert(Pred);
			}
			CFGMap[&BB] = predSet;
		}

		return CFGMap;
	}


	// std::map<BasicBlock *, std::set<BasicBlock *>> computeDominators(Function &F) {
	// 	std::map<BasicBlock *, std::set<BasicBlock *>> dominators;
	// 	std::set<BasicBlock *> allBlocks;

	// 	for (BasicBlock &BB : F) {
	// 		allBlocks.insert(&BB);
	// 	}

	// 	for (BasicBlock &BB : F) {
	// 		if (&BB == &F.getEntryBlock()) {
	// 			dominators[&BB].insert(&BB);
	// 		} else {
	// 			dominators[&BB] = allBlocks;
	// 		}
	// 	}

	// 	bool changed = true;
	// 	while (changed) {
	// 		changed = false;
	// 		for (BasicBlock &BB : F) {
	// 			if (&BB == &F.getEntryBlock())
	// 				continue;

	// 			std::set<BasicBlock *> intersectionSet = allBlocks;
	// 			for (auto *Pred : predecessors(&BB)) {
	// 				std::set<BasicBlock *> tempSet;
	// 				std::set_intersection(intersectionSet.begin(), intersectionSet.end(),
	// 									dominators[Pred].begin(), dominators[Pred].end(),
	// 									std::inserter(tempSet, tempSet.begin()));
	// 				intersectionSet = tempSet;
	// 			}

	// 			intersectionSet.insert(&BB);
	// 			if (dominators[&BB] != intersectionSet) {
	// 				dominators[&BB] = intersectionSet;
	// 				changed = true;
	// 			}
	// 		}
	// 	}

	// 	return dominators;
	// }

	std::map<BasicBlock *, std::set<BasicBlock *>> computeDominators(Function &F, std::map<BasicBlock *, std::set<BasicBlock *>> &CFG) {
		std::map<BasicBlock *, std::set<BasicBlock *>> dominators;
		std::set<BasicBlock *> allBlocks;

		for (BasicBlock &BB : F) {
			allBlocks.insert(&BB);
		}

		for (BasicBlock &BB : F) {
			if (&BB == &F.getEntryBlock()) { // For reversed CFG, this should be the exit block.
				dominators[&BB].insert(&BB);
			} else {
				dominators[&BB] = allBlocks;
			}
		}

		bool changed = true;
		while (changed) {
			changed = false;
			for (BasicBlock &BB : F) {
				if (&BB == &F.getEntryBlock()) // For reversed CFG, this should be the exit block.
					continue;

				std::set<BasicBlock *> intersectionSet = allBlocks;
				for (BasicBlock *Pred : CFG[&BB]) { // Use the provided CFG here
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

		auto predecessors = createCFGMap(F);
		auto dominators = computeDominators(F, predecessors);
		// auto dominators = computeDominators(F);
		auto dominatedBlocks = computeDominatedBlocks(F, dominators);
		auto immediateDominators = computeImmediateDominators(F, dominators);

		// auto reversedCFG = reverseCFG(F);
		// auto postDominators = computeDominators(F, reversedCFG);
		// auto postDominatedBlocks = computeDominatedBlocks(F, postDominators);
		// auto postImmediateDominators = computeImmediateDominators(F, postDominators);

		// Put all basic blocks into a vector for sorting for alphabetized output
		std::vector<BasicBlock*> blocks;
		for (BasicBlock &BB : F) {
			blocks.push_back(&BB);
		}

		// Sort the vector by the names of the blocks
		std::sort(blocks.begin(), blocks.end(),
			[](const BasicBlock *a, const BasicBlock *b) -> bool {
				return a->getName() < b->getName();
			}
		);

		// Iterate over the sorted vector to print the information
		for (BasicBlock *BB : blocks) {
			// Print the basic block name
			errs() << BB->getName() << ":\n";

			// Print dominated blocks
			auto &dominatedSet = dominatedBlocks[BB];
			errs() << "    "; // Indent the line
			std::vector<std::string> dominatedNames;
			for (BasicBlock *DominatedBB : dominatedSet) {
				dominatedNames.push_back(DominatedBB->getName().str());
			}
			std::sort(dominatedNames.begin(), dominatedNames.end());
			for (const auto &name : dominatedNames) {
				errs() << name << " ";
			}
			errs() << "\n";

			// Print immediate dominator
			BasicBlock *iDom = immediateDominators[BB];
			errs() << "    " << (iDom ? iDom->getName() : "X") << "\n";
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
