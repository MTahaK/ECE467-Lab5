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

using namespace llvm;
using namespace std;

namespace {

// This method implements what the pass does
void processFunction(Function &F) {
    // ECE467 STUDENT: add your code here
}

struct A5Dom : PassInfoMixin<A5Dom> {
  // This is the main entry point for processing the IR of a function
  // It simply calls the function that has your code
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
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
llvm::PassPluginLibraryInfo getA5DomPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "A5Dom", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "A5Dom") {
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
llvmGetPassPluginInfo() {
  return getA5DomPluginInfo();
}
