//===------------------------- IdentifyRegions.h -------------------------===//
//
//                     The LLVM Compiler Infrastructure
// 
// This file is distributed under the Università della Svizzera italiana (USI) 
// Open Source License.
//
// Author         : Georgios Zacharopoulos 
// Date Started   : November, 2015
//
//===----------------------------------------------------------------------===//
//
// This file identifies Single-Input, Single-Output Regions in a CFG of an
// application and computes the Data Flow Input and Output for each Region. 
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "IdentifyRegions"

using namespace llvm;

std::ofstream region_info_latex; // File that Region Info are written.

namespace {
  int find_bb_name(std::vector<BasicBlock *> list, BasicBlock *BB) {

      for (unsigned i = 0; i < list.size(); i++)
        if (list[i]->getName() == BB->getName())
          return i;
      
    
    return -1;
  }


  // int find_inst(std::vector<Instruction *> list, Instruction *inst) { // Remove it since there is in IdentifyRegions.h

  //     for (unsigned i = 0; i < list.size(); i++)
  //       if (list[i] == inst)
  //         return i;
      
    
  //   return -1;
  // }

  int find_op(std::vector<Value *> list, Value *op) {

      for (unsigned i = 0; i < list.size(); i++) 
        if (list[i] == op)
          return i;
      
    
    return -1;
  }

  int find_array(std::vector<Value *> ArrayReferences, Value *ArrayRef) {

    for (unsigned i = 0; i < ArrayReferences.size(); i++) 
      if (ArrayReferences[i] == ArrayRef)
        return i;
      
    
    return -1;
  }

  int find_region(std::vector<Region *> list, Region *Reg) {

    for (unsigned i = 0; i < list.size(); i++)
      if (list[i] == Reg)
        return i;
      
    
    return -1;
  }
    

  // int find_bb(std::vector<BasicBlock *> list, BasicBlock *BB) {

  //   for (unsigned i = 0; i < list.size(); i++)
  //     if (list[i] == BB)
  //       return i;
      
    
  //   return -1;
  // }



  bool printBasicBlock(Region::block_iterator &BB) {

    errs() << "     BB Name\t\t\t:\t" << BB->getName() << " \n";

    return false;
  }

  // Returns true if Block iterator of Region contains no Call Instructions.
  //
  bool isBBCallFree(Region::block_iterator &BB) {

    // Iterate inside the basic block.
    for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI){
       if(dyn_cast<CallInst>(&*BI))
        return false;
    }

    return true;
  }

  // Region Function - Might remove it.
  //
  bool runOnBasicBlock(Region::block_iterator &BB, unsigned int *DFGNodesRegion, unsigned int *GoodDFGNodesRegion, unsigned int *OptimalityRegion) {

      unsigned int GoodDFGNodesBB = 0;
      unsigned int GoodnessBB = 0;
      int32_t freq = 0; 

      // Iterate inside the basic block.
      for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {
        
        *DFGNodesRegion = *DFGNodesRegion + 1;

        if (!isMarked(&*BI)) {
          *GoodDFGNodesRegion = *GoodDFGNodesRegion + 1;
          GoodDFGNodesBB++;
        }
      }

      if (MDNode *node = BB->getTerminator()->getMetadata("freq")) {

        if (MDString::classof(node->getOperand(0))) {
          auto mds = cast<MDString>(node->getOperand(0));
          std::string metadata_str = mds->getString();
          freq = std::stoi(metadata_str);
        }

      }

      GoodnessBB = GoodDFGNodesBB * freq ;
      *OptimalityRegion = *OptimalityRegion + GoodnessBB; // Density

      // errs() << "     Good Nodes of BB are\t:\t" << GoodDFGNodesBB << " \n";
      // errs() << "     Frequency of BB is  \t:\t" << freq << " \n";
      // errs() << "     Goodness of BB is   \t:\t" << GoodnessBB << " \n\n";
      
      //++BBCounter;
      return false;
  }

  // Get Area Estimation for a Block iterator of a Region.
  unsigned int getAreaOfBB(Region::block_iterator &BB) {

    unsigned int AreaOfBB = 0;

    // Iterate inside the basic block.
    for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI)
      AreaOfBB += getAreaEstim(&*BI);

    return AreaOfBB;
  }

  // Get the Area extimation of a Region in LUTs.
  unsigned int getAreaofRegion(Region *R){

    unsigned int AreaOfRegion = 0;

    for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB)
      AreaOfRegion += getAreaOfBB(BB);

    return AreaOfRegion;

  }

  
  // Region Function - Might remove it.
  //
  bool getGoodnessAndDensityOfRegionInBB(Region::block_iterator &BB, unsigned int *DFGNodesRegion, unsigned int *GoodDFGNodesRegion, unsigned int *OptimalityRegion) {

    unsigned int GoodDFGNodesBB = 0;
    unsigned int GoodnessBB = 0;
    int32_t freq = 0; 

    // Iterate inside the basic block.
    for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {
      
      *DFGNodesRegion = *DFGNodesRegion + 1;

      if (!isMarked(&*BI)) {
        *GoodDFGNodesRegion = *GoodDFGNodesRegion + 1;
        GoodDFGNodesBB++;
      }
    }

    if (MDNode *node = BB->getTerminator()->getMetadata("freq")) {

      if (MDString::classof(node->getOperand(0))) {
        auto mds = cast<MDString>(node->getOperand(0));
        std::string metadata_str = mds->getString();
        freq = std::stoi(metadata_str);
      }

    }

    GoodnessBB = GoodDFGNodesBB * freq ;
    *OptimalityRegion = *OptimalityRegion + GoodnessBB; 
    
    return false;
  }

  // Gather the number of BBs in a Region.
  unsigned int getBBsOfRegion(Region *R) {

    unsigned int BBsofRegion=0;

    for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB)
      BBsofRegion++;

    return BBsofRegion;
  }


  // Gather the number of DFG Nodes in a Region.
  unsigned int getDFGNodesOfRegion(Region *R) {

    unsigned int DFGNodes=0;

    for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB){

      for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI)
        DFGNodes++;
    }

    return DFGNodes;
  }

  // Gather the number of Loops in a Region.
  unsigned int getLoopsOfRegion(Region *R, LoopInfo &LI) {

    unsigned int NumberOfLoops=0;
    std::vector<Loop *> Loops;
    Loops.clear();

    for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB){

      if (Loop *L = LI.getLoopFor(*BB)){

      if (find_loop(Loops, L) == -1 ){ 
          Loops.push_back(L);
          NumberOfLoops++;
        }
      }
    }

    return NumberOfLoops;
  }

}
