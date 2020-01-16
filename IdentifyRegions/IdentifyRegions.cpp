//===------------------------- IdentifyRegions.cpp -------------------------===//
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

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/RegionPass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BlockFrequencyInfoImpl.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Transforms/Utils/Local.h"
#include <string>
#include <iostream>
#include <fstream>
#include <algorithm>
#include "llvm/IR/CFG.h"
#include "../Identify.h" // Header file for all 3 passes. (IdentifyRegions, IdentifyBbs, IdentifyFunctions)
#include "IdentifyRegions.h"

#define DEBUG_TYPE "IdentifyRegions"

#define User_Input    100  // # of Scalar Instructions (Operands)
#define User_Output   100 // # of Scalar Instructions (Operands)


STATISTIC(RegionCounter, "The # of Regions Identified");

using namespace llvm;

namespace {

  struct IdentifyRegions : public FunctionPass {
    static char ID; // Pass Identification, replacement for typeid

    IdentifyRegions() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {

      std::vector<Region *> Region_list;
      std::vector<BasicBlock*> BB_list;
      std::vector<unsigned int> Goodness_list, Density_list;
      Region_list.clear();
      Goodness_list.clear();
      Density_list.clear();
      BB_list.clear();

      RegionInfo *RI = &getAnalysis<RegionInfoPass>().getRegionInfo();

      errs() << "\n\nFunction Name is : " << F.getName() << "\n";

      // Iterate over Regions in the Function
      for(Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {

        if (Region *R = RI->getRegionFor(&*BB)) {

          if (isRegionValid(R) && find_region(Region_list, R) == -1) {
            Region_list.push_back(R);
            Goodness_list.push_back(getGoodnessOfRegion(R));
            Density_list.push_back(getDensityOfRegion(R));

            RegionAnalysis(R);
          }
        }
	
	// Print the DFG Graphs.
	//DFGPrinterBB(&*BB); // Activate to print the DFG graphs.

      }

      errs() << "   Valid Regions are : " << "\n" ;
      for (int i=0; i< Region_list.size(); i++)
        errs() << " Goodness " << Goodness_list[i] << " Density " << Density_list[i] 
            << "   Reg_Name " << Region_list[i]->getEntry()->getName() << " => " << Region_list[i]->getExit()->getName()
	    //Region_list[i]->getNameStr() 
	    << "\n" ;

      return false;
    }
    

    void printBBRegionList(Region *R, std::vector<BasicBlock *> BB_list) {

     // errs() << "BB_list " ; 

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        //errs() << find_bb(BB_list, *BB) << " ";

        myfile.open ("Regions.txt", std::ofstream::out | std::ofstream::app); 
        myfile << find_bb(BB_list, *BB)  << "," ;
        myfile.close();


      }

      //errs() << "\n" ; 

      myfile.open ("Regions.txt", std::ofstream::out | std::ofstream::app); 
      myfile << "\n" ;
      myfile.close();
      
    }

    virtual unsigned int getGoodnessOfRegion(Region *R) {

      unsigned int DFGNodesRegion = 0;
      unsigned int GoodDFGNodesRegion = 0;
      unsigned int GoodnessRegion = 0;


      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB)
        getGoodnessAndDensityOfRegionInBB(BB, &DFGNodesRegion, &GoodDFGNodesRegion, &GoodnessRegion);

      return GoodnessRegion;

    }

     virtual unsigned int getDensityOfRegion(Region *R) {

      unsigned int DFGNodesRegion = 0;
      unsigned int GoodDFGNodesRegion = 0;
      unsigned int GoodnessRegion = 0;
      unsigned int DensityRegion = 0;


      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB)
        getGoodnessAndDensityOfRegionInBB(BB, &DFGNodesRegion, &GoodDFGNodesRegion, &GoodnessRegion);


      DensityRegion = static_cast<unsigned int> (GoodnessRegion / DFGNodesRegion) ; // Density of the Region.

      return DensityRegion;
    }

    // Get the Area extimation of a Region in LUTs.
    unsigned int getAreaofRegion(Region *R){

      unsigned int AreaOfRegion = 0;

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB)
        AreaOfRegion += getAreaOfBB(BB);

      return AreaOfRegion;

    }

    // Get the Delay Estimation for the Region.
    //
    //
    long int getHWCostOfRegion(Region *R) {

      float DelayOfRegion, DelayOfRegionTotal = 0;
      long int HardwareCost =0;
      BlockFrequencyInfo *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI(); 
      std::vector<BasicBlock *> worklist, predecessor_bb, successor_bb;
      std::vector<float> BBFreqPerIter;
      std::vector<float> BBFreqTotal;
      std::vector<float> DelayRegionPathsPerIter, DelayRegionPathsTotal;
      std::vector<long int>   HWCostPath, HWCostBB;

      // Clear vectors.
      worklist.clear();
      predecessor_bb.clear();
      successor_bb.clear();
      BBFreqPerIter.clear();
      BBFreqTotal.clear();
      DelayRegionPathsPerIter.clear();
      DelayRegionPathsTotal.clear();
      HWCostPath.clear();
      HWCostBB.clear();

      // Populate worklist with Region's Basic Blocks and their respective BB's Frequencies. Both Per Iteration and Total.
      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        float BBFreqFloat = static_cast<float>(static_cast<float>(BFI->getBlockFreq(*BB).getFrequency()) / static_cast<float>(BFI->getEntryFreq()));
        int EntryFuncFreq = getEntryCount(R->block_begin()->getParent());
        float BBFreq = BBFreqFloat * static_cast<float>(EntryFuncFreq);
        
        worklist.push_back(*BB);
        BBFreqPerIter.push_back(BBFreqFloat);
        BBFreqTotal.push_back(BBFreq);
        HWCostBB.push_back(ceil( ( getDelayOfBB(*BB) ) / NSECS_PER_CYCLE ) * BBFreqTotal[find_bb(worklist, *BB)] ); // HW Cost for each BB (Cyclified) 
        HWCostPath.push_back(ceil( ( getDelayOfBB(*BB) ) / NSECS_PER_CYCLE ) * BBFreqTotal[find_bb(worklist, *BB)] );

    
      }

      errs() << "\n";
      for (int i=0; i< worklist.size(); i++) {
        errs() << " BBs in Region " << worklist[i]->getName() << " Freq per Iter " << BBFreqPerIter[i] <<  
          " Freq Total " << BBFreqTotal[i] << " HW Cost BB " << HWCostBB[i] << "\n"; // My debugging Info!    
      }

      // Region has more than one BBs.
      if (worklist.size() > 1) {

        // Find Relations among BBs.
        //
        // Predecessor --> Successor
        //
        //
        int count =0;  
        
        for (std::vector<BasicBlock *>::iterator bb_iter = worklist.begin(); bb_iter != worklist.end(); ++bb_iter, count++) {

          if(BasicBlock *BB = *bb_iter) {
            // Getting the Succeror BBs of each BB in the worklist.
            for (succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) { 
              
              BasicBlock *Succ = *SI;      
      
              // if(count < find_bb(worklist, Succ) ) {  /// !!! CHANGED THIS !!!!!!
              if(count != find_bb(worklist, Succ) ) { 
                predecessor_bb.push_back(BB); // Populate send_node vector
                successor_bb.push_back(Succ); // Populate receive_node vector
              }
            }
          }
        }

        errs() << "\n\n"  ;
        for (int i=0; i< predecessor_bb.size(); i++) {
          errs() << " BB Edges in the Region : " << predecessor_bb[i]->getName() << "  --->     " <<  successor_bb[i]->getName() << "\n"; // My debugging Info!
        }
        errs() << "\n" ;

        
        // BEGIN OF WORK IN PROGRESS

        // WORKING ON THAT!!!
        int pos_successor = 0;
        for (std::vector<BasicBlock *>::iterator succ_iter = successor_bb.begin(); succ_iter != successor_bb.end(); ++succ_iter, pos_successor++) {
            BasicBlock *successor = *succ_iter;

            errs() << "Counter : " << pos_successor << "\n" ;


            if (find_bb(worklist, successor) == -1) {                       // Succesor is *not* in our worklist.

              successor_bb.erase(successor_bb.begin() + pos_successor);             // deleting the edge
              predecessor_bb.erase(predecessor_bb.begin() + pos_successor);        //  deleting the edge
              succ_iter--;          // Be careful!!!
              pos_successor--;       // Be careful!!!
              continue;
            }

            int succ_pos_in_pred_list = find_bb(predecessor_bb, successor);
            errs() << "  Successor position in pred list : " << succ_pos_in_pred_list << "\n";

            if ( succ_pos_in_pred_list > pos_successor || succ_pos_in_pred_list == -1)        // Maybe put >= instead of >
              continue;


            int new_position = find_bb(successor_bb, predecessor_bb[pos_successor]);  


              errs() << " Begin" << "\n";
              errs() << " new_position " << new_position << "\n";
              errs() << " position successor " << pos_successor << "\n";    


            while (new_position < pos_successor && new_position !=-1) {

              errs() << " new_position : " << new_position << "\n";
              errs() << " position successor : " << pos_successor << "\n";

              //int new_pos = find_bb(successor_bb, predecessor_bb[pos_successor]);

              if (predecessor_bb[new_position] == successor) {

                successor_bb.erase(successor_bb.begin() + pos_successor);             // deleting the edge
                predecessor_bb.erase(predecessor_bb.begin() + pos_successor);        //  deleting the edge
                succ_iter--;            // Be careful!!!
                pos_successor--;         // Be careful!!!
                new_position = pos_successor; // End the search. Maybe insert a break.
              }

              else
                new_position = find_bb(successor_bb, predecessor_bb[new_position]); 

            }


        }

        // END OF WORK IN PROGRESS

        errs() << "\n\n   Updated Edges \n"  ;
        for (int i=0; i< predecessor_bb.size(); i++) {
          errs() << " BB Edges in the Region : " << predecessor_bb[i]->getName() << "  --->     " <<  successor_bb[i]->getName() << "\n"; // My debugging Info!
        }
        errs() << "\n" ;


        // Critical Path Estimation. 
        //       
        // 
        for (std::vector<BasicBlock *>::iterator bb_iter = worklist.begin(); bb_iter != worklist.end(); ++bb_iter) {

          BasicBlock *BB = *bb_iter;

          // Find the end Nodes - Bottom-most Nodes (BBs) in the CFG Graph.
          if (find_bb(predecessor_bb, BB) == -1) {

            BasicBlock *EndNode = BB;
            std::vector<BasicBlock *> BottomNodes;
            BottomNodes.clear();
            BottomNodes.push_back(EndNode);


            BasicBlock *CurrentNode;
            int position, position_bottom_nodes = 0;
  
            long int hw_cost;  // Remove it when you are done!

            while(BottomNodes.size()>0) {  
             
                CurrentNode = BottomNodes[0];
     
                errs() << " \n\nCurrentNode " << CurrentNode->getName() << "\n";
                errs() << " \nBottom List Size " << BottomNodes.size() << "\n";
                
                
                while (find_bb(successor_bb, CurrentNode) >=0) {

                  position = find_bb(successor_bb, CurrentNode); 
                  position_bottom_nodes = find_bb(BottomNodes, CurrentNode); // Should be zero.


                  errs()  << CurrentNode->getName() << " " << HWCostPath[find_bb(worklist, CurrentNode)] ;
                  errs() << " --> " << predecessor_bb[position]->getName() << " " << HWCostPath[find_bb(worklist, predecessor_bb[position])] << "\n";
                  errs() << "Original \n" << CurrentNode->getName() << " " << HWCostPath[find_bb(worklist, CurrentNode)] ;
                  errs() << " --> " << predecessor_bb[position]->getName() << " " << HWCostBB[find_bb(worklist, predecessor_bb[position])] << "\n";


                  HWCostPath[find_bb(worklist, predecessor_bb[position])] = std::max( HWCostPath[find_bb(worklist, predecessor_bb[position])], HWCostBB[find_bb(worklist, predecessor_bb[position])] + HWCostPath[find_bb(worklist, CurrentNode)] );
                  errs() << " Updated " << predecessor_bb[position]->getName() << " " << HWCostPath[find_bb(worklist, predecessor_bb[position])];
                  
                  BasicBlock *Predecessor = predecessor_bb[position];

                  successor_bb.erase(successor_bb.begin() + position);            // deleting the last edge
                  predecessor_bb.erase(predecessor_bb.begin() + position);        //  deleting the last edge
                  
                  errs() << "\nPredecessor in pred list  " <<  Predecessor->getName() << " " << find_bb(predecessor_bb, Predecessor) << "\n";

                  if (find_bb(predecessor_bb, Predecessor) == -1)
                    BottomNodes.push_back(Predecessor);
                  

                }

                //BottomNodes.erase(BottomNodes.begin()+ position_bottom_nodes);
                BottomNodes.erase(BottomNodes.begin());
                errs() <<  "\n";
                
                errs() << " Bottom Nodes in list : \n" ;
                for (int i=0; i< BottomNodes.size(); i++) {
                  errs() << " Node : " << BottomNodes[i]->getName()  << "\n"; // My debugging Info!
                }

            }
          }
        }

        HardwareCost       = get_max_long_int(HWCostPath);                // Total Cycles spent on HW.
      }

      // In case that the Region has only one BB.
      // else if (worklist.size() == 1) {
      else {
        //DelayOfRegion      = getDelayOfBB(worklist[0]) * BBFreqPerIter[0];
        //DelayOfRegionTotal = getDelayOfBB(worklist[0]) * BBFreqTotal[0];
        HardwareCost       = ceil( ( getDelayOfBB(worklist[0]) ) / NSECS_PER_CYCLE ) * BBFreqTotal[0];
      }



      return HardwareCost;
    }

    // Get the Delay Estimation for the Region.
    //
    //
    float getDelayOfRegion(Region *R) {

      float DelayOfRegion, DelayOfRegionTotal = 0;
      BlockFrequencyInfo *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI(); 
      std::vector<BasicBlock *> worklist, predecessor_bb, successor_bb;
      std::vector<float> BBFreqPerIter;
      std::vector<float> BBFreqTotal;
      std::vector<float> DelayRegionPathsPerIter, DelayRegionPathsTotal;

      // Clear vectors.
      worklist.clear();
      predecessor_bb.clear();
      successor_bb.clear();
      BBFreqPerIter.clear();
      BBFreqTotal.clear();
      DelayRegionPathsPerIter.clear();
      DelayRegionPathsTotal.clear();

      // Populate worklist with Region's Basic Blocks and their respective BB's Frequencies. Both Per Iteration and Total.
      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        float BBFreqFloat = static_cast<float>(static_cast<float>(BFI->getBlockFreq(*BB).getFrequency()) / static_cast<float>(BFI->getEntryFreq()));
        int EntryFuncFreq = getEntryCount(R->block_begin()->getParent());
        float BBFreq = BBFreqFloat * static_cast<float>(EntryFuncFreq);
        
        worklist.push_back(*BB);
        BBFreqPerIter.push_back(BBFreqFloat);
        BBFreqTotal.push_back(BBFreq);
      }

      // errs() << "\n";
      // for (int i=0; i< worklist.size(); i++) {
      //   errs() << " BBs in Region " << worklist[i]->getName() << " Freq per Iter " << BBFreqPerIter[i] <<  
      //     " Freq Total " << BBFreqTotal[i] << "\n"; // My debugging Info!    
      // }

      // Region has more than one BBs.
      if (worklist.size() > 1) {

        // Find Relations among BBs.
        //
        // Predecessor --> Successor
        //
        //
        int count =0;  
        
        for (std::vector<BasicBlock *>::iterator bb_iter = worklist.begin(); bb_iter != worklist.end(); ++bb_iter, count++) {

          if(BasicBlock *BB = *bb_iter) {
            // Getting the Succeror BBs of each BB in the worklist.
            for (succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) { 
              
              BasicBlock *Succ = *SI;      
      
              if(count < find_bb(worklist, Succ) ) { 

                predecessor_bb.push_back(BB); // Populate send_node vector
                successor_bb.push_back(Succ); // Populate receive_node vector
              }
            }
          }
        }

        // errs() << "\n\n"  ;
        // for (int i=0; i< predecessor_bb.size(); i++) {
        //   errs() << " BB Edges in the Region : " << predecessor_bb[i]->getName() << "  --->     " <<  successor_bb[i]->getName() << "\n"; // My debugging Info!
        // }



        // Critical Path Estimation. 
        //       
        // 
        for (std::vector<BasicBlock *>::iterator bb_iter = worklist.begin(); bb_iter != worklist.end(); ++bb_iter) {

          BasicBlock *BB = *bb_iter;

          // Find the end Nodes - Bottom-most Nodes (BBs) in the CFG Graph.
          if (find_bb(predecessor_bb, BB) == -1) {

            BasicBlock *EndNode = BB;

            BasicBlock *CurrentNode;
            int position;
            float delay_path_estimation, delay_path_estimation_total;

            while(find_bb(successor_bb, EndNode)>=0) {  

              CurrentNode = EndNode;
              position= 0;
              delay_path_estimation= getDelayOfBB(CurrentNode) * BBFreqPerIter[find_bb(worklist, CurrentNode)];
              delay_path_estimation_total = getDelayOfBB(CurrentNode) * BBFreqTotal[find_bb(worklist, CurrentNode)];

              while (find_bb(successor_bb, CurrentNode) >=0) {

                position = find_bb(successor_bb, CurrentNode); 
                delay_path_estimation = delay_path_estimation + (getDelayOfBB(predecessor_bb[position]) * BBFreqPerIter[find_bb(worklist, predecessor_bb[position])]);
                delay_path_estimation_total = delay_path_estimation_total + (getDelayOfBB(predecessor_bb[position]) * BBFreqTotal[find_bb(worklist, predecessor_bb[position])]);
                CurrentNode = predecessor_bb[position];

                // errs() << "Delay for this node " << format("%.8f", getDelayEstim(send_node[position])) << "\n"; // My debugging Info!    
                // errs() << "Delay path estim    " <<  format("%.8f", delay_path_estimation ) << "\n"; // My debugging Info!
                // errs() << " Current Node is:   " << *CurrentNode << "\n";
              }

              // errs() << "Delay path estim    " <<  format("%.8f", delay_path_estimation ) << "\n"; // My debugging Info!
              DelayRegionPathsPerIter.push_back(delay_path_estimation);
              DelayRegionPathsTotal.push_back(delay_path_estimation_total);
              successor_bb.erase(successor_bb.begin() + position);   // deleting the last edge
              predecessor_bb.erase(predecessor_bb.begin() + position);        //  deleting the last edge

              
            }
          }
        }

        DelayOfRegion = get_max(DelayRegionPathsPerIter);       // Per Iteration.
        DelayOfRegionTotal = get_max(DelayRegionPathsTotal);    // Total Delay.
      }

      // In case that the Region has only one BB.
      // else if (worklist.size() == 1) {
      else {
        DelayOfRegion      = getDelayOfBB(worklist[0]) * BBFreqPerIter[0];
        DelayOfRegionTotal = getDelayOfBB(worklist[0]) * BBFreqTotal[0];
      }

 

      // errs() << " Delay Estimation for Region per Iteration is : " << format("%.8f", DelayOfRegion)      << " nSecs" << "\n";
      // errs() << " Delay Estimation for Region Total         is : " << format("%.8f", DelayOfRegionTotal) << " nSecs" << "\n";

      // errs() << " DEPI " << format("%.8f", DelayOfRegion);
      // errs() << " DET " << format("%.8f", DelayOfRegionTotal) << " ";


      return DelayOfRegionTotal;
    }


    // Check to see if Region is Valid.
    virtual bool isRegionValid(Region *R) {

      if (R->getExit()) { // Check for Exit Block

        // Gather the input Data Flow for the Region.
        int Input = gatherInput(R);

        // Gather the output Data Flow for the Region.
        //
        // We do not consider the whole function as possible Region.
        // So Exit Block should not be NULL. (ExitBlock != NULL)
        int Output = gatherOutput(R);

        // Check if specified I/O Constraints are met.
        if (isRegionCallFree(R))
          return true;

      }

      return false;
    }

    // Check to see if Region is Valid.
    virtual bool isRegionCallFree(Region *R) {

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) 
        if(!isBBCallFree(BB))
          return false;

      return true;
    }

    float getRegionTotalFreq (Region *R) {

      
      BlockFrequencyInfo *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
      float RegionFreq = 0;
      bool backedge = false;
      Region::block_iterator BB_it_entry = R->block_begin();
      BasicBlock * BB_entry = *BB_it_entry;
      Function   *FunctionOfBB_entry = BB_entry->getParent();


      float BBEntryFreqFloat = static_cast<float>(static_cast<float>(BFI->getBlockFreq(BB_entry).getFrequency()) / static_cast<float>(BFI->getEntryFreq()));
      int EntryFuncFreq = getEntryCount(FunctionOfBB_entry);
      float BBEntryFreq = BBEntryFreqFloat * static_cast<float>(EntryFuncFreq); // Freq_Total


      // Case Entry of Region is Entry of Function.
      if (BB_entry == FunctionOfBB_entry->begin())
        return static_cast<float>(EntryFuncFreq);


      if (BB_entry->getSinglePredecessor())
        return BBEntryFreq;
      
      //else {
        for (pred_iterator PI = pred_begin(BB_entry), PE = pred_end(BB_entry); PI != PE; ++PI) {

          BasicBlock *BB_pred = *PI;
          
          if (R->contains(BB_pred)) {
            backedge = true;
            continue;
          }

          if (BranchInst *Branch = dyn_cast<BranchInst>(&*BB_pred->getTerminator())) {

            if (Branch->isUnconditional()) {

              float BBPredFreqFloat = static_cast<float>(static_cast<float>(BFI->getBlockFreq(BB_pred).getFrequency()) / static_cast<float>(BFI->getEntryFreq()));
              int   PredFuncFreq = getEntryCount(FunctionOfBB_entry);
              float BBPredFreq = BBPredFreqFloat * static_cast<float>(PredFuncFreq); // Freq_Total  

              RegionFreq += BBPredFreq;
            }
          }
        }

        if (!backedge)
          return BBEntryFreq;

        return RegionFreq;
    }

   // Software Cost for Regions Estimation.  **NEW**
   //
   long int getCostOnSoftwareRegion(Region *R) {

      Region::block_iterator BB_begin = R->block_begin();
      Function   *FunctionOfBB = BB_begin->getParent();

      BlockFrequencyInfo *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
      long int Cost_Software_Region = 0;

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        long int Cost_Software_BB = 0;
        float BBFreqFloat = static_cast<float>(static_cast<float>(BFI->getBlockFreq(*BB).getFrequency()) / static_cast<float>(BFI->getEntryFreq()));
        int EntryFuncFreq = getEntryCount(FunctionOfBB);
        float BBFreq = BBFreqFloat * static_cast<float>(EntryFuncFreq);

        // Calculate the Software Cost in Cycles multiplied with the respective frequency of the BB.
        Cost_Software_BB = static_cast<long int> (getSWCostOfBB(*BB) * BBFreq);
        Cost_Software_Region += Cost_Software_BB;
      }

      return Cost_Software_Region;
    }

    void PrintRegion(Region *R) {



      Region::block_iterator BB = R->block_begin();
      Function   *FunctionOfBB = BB->getParent();


      unsigned int BBRegionCounter = 0;
      unsigned int DFGNodesRegion = 0;
      unsigned int GoodDFGNodesRegion = 0;

      // Goodness and Density
      unsigned int   OptimalityRegion = 0;
      float DensityRegion = 0;
      unsigned int AreaOfRegion = getAreaofRegion(R);
      float RegionFreq           = getRegionTotalFreq(R);
      float DelayOfRegion        = getDelayOfRegion(R);
      float DelayOfRegionPerIter = getDelayOfRegionPerIter(R);

      // Costs to calculate Speedup.
      long int Cost_Software = 0;
      long int Cost_Hardware = 0;
      long int Overhead      = 0;

      std::vector<BasicBlock *> BB_list; // Worklist for Basic Blocks in Region.
      BB_list.clear();

      errs() << "\n\n"; 
      
      // if (R->isSimple()) {
      //   errs() << "   Simple Region **** "  << "\n";
      //   ++SimpleRegionCounter;
      // }
      errs() << "   **********************************************************************************" << '\n';
      errs() << "   Function Name is : " << FunctionOfBB->getName() << "\n";
      errs() << "   Region Depth  is : " << R->getDepth() << "\n";
      	//if(!R->getNameStr().empty())
      	//	errs() << "   Region Name   is : " << R->getNameStr() << "\n\n";
     	// 	errs() << "   Region Name   is : " << R->getEnteringBlock()->getName() << 
	//       R->getExitingBlock()->getName()	<< "\n\n";
      errs() << "   Region Name   is : " << R->getEntry()->getName() << " => " << R->getExit()->getName() << "\n\n";

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        //printBasicBlock(BB);
        runOnBasicBlock(BB, &DFGNodesRegion, &GoodDFGNodesRegion, &OptimalityRegion);
        //getCostOnSoftware(BB, &Cost_Software);
        ++BBRegionCounter;

        BB_list.push_back(*BB);
  
      }

      errs() << "We are here! \n" ;

      DensityRegion = OptimalityRegion / DFGNodesRegion; // Density of the Region.

      Cost_Software = static_cast<long int> (getCostOnSoftwareRegion(R));
      Cost_Hardware = static_cast<long int> (getHWCostOfRegion(R));
      Overhead      = static_cast<long int> (RegionFreq * CALL_ACC_OVERHEAD);

      // Final "Speedup" of a Region.
      long int Speedup = Cost_Software - Cost_Hardware - Overhead;



      errs() << "   -------------------------------------------------------------" << '\n';
      errs() << "\n     BB Number is              : " << BBRegionCounter << "\n";
      errs() << "     Good DFG Nodes are        : " << GoodDFGNodesRegion << "\n" ; 
      errs() << "     DFG Nodes Number is       : " << DFGNodesRegion << "\n\n";
      errs() << "     Optimality of Region is   : " << OptimalityRegion << "\n";
      //errs() << "     Density of Region is      : " << DensityRegion << "\n\n";
      errs() << "   -------------------------------------------------------------" << '\n';
   
      errs() << "Good " << OptimalityRegion << " Dens " << static_cast<int>(DensityRegion) << " Func " << 
        FunctionOfBB->getName() << " Reg " << 
	//R->getNameStr()  // Replaced it because of synbol lookup error
 	R->getEntry()->getName() <<" => " << R->getExit()->getName()
	<< " Speedup " << Speedup << " Cost_Software " << Cost_Software << 
         " Cost_Hardware " << Cost_Hardware << " Overhead " << Overhead << " Area " << AreaOfRegion << "\n"  ;

     // Write Regions Identified in Regions.txt file.
     std::string FuncName   = FunctionOfBB->getName(); 
     //std::string RegionName = R->getNameStr(); // Replaced it because of synbol lookup error
     std::string entryName = R->getEntry()->getName();
     std::string exitName = R->getExit()->getName();
     std::string RegionName = entryName + " => " + exitName;

      myrawfile.open ("Regions_raw.txt", std::ofstream::out | std::ofstream::app); 
      myrawfile << FuncName <<  "\t" << RegionName << "\t"  << AreaOfRegion << "\t";

      myrawfile << static_cast<int>(RegionFreq) << "\t";
      myrawfile << Speedup << "\t";
      myrawfile << Cost_Software << "\t";
      myrawfile << Cost_Hardware << " \t" << "\n";
      myrawfile.close();

     myfile.open ("Regions.txt", std::ofstream::out | std::ofstream::app); 
     myfile << FuncName << " " << RegionName << " "<< Speedup << " " << AreaOfRegion << " " ;
     myfile.close();

  }

  void PrintRegionInfo(Region *R) {

    // Loop Information
    LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    Region::block_iterator BB = R->block_begin();
    Function   *FunctionOfBB  = BB->getParent();

    // Gather Region Info
    std::string FuncName       = FunctionOfBB->getName(); 
    //std::string RegionName = R->getNameStr(); // Replaced it because of synbol lookup error
    std::string entryName = R->getEntry()->getName();
    std::string exitName = R->getExit()->getName();
    std::string RegionName = entryName + " => " + exitName;
    unsigned int NumberOfBBs   = getBBsOfRegion(R);
    unsigned int NumberOfLoops = getLoopsOfRegion(R, LI);
    unsigned int NumberOfDFGNodes = getDFGNodesOfRegion(R);

    // Write Region Info to the file.
    region_info_latex.open ("Region_info_latex.txt", std::ofstream::out | std::ofstream::app); 
    region_info_latex << "$" <<FuncName << "$" << " & "  <<RegionName << " & " << NumberOfLoops << " & " <<  NumberOfBBs << " & " << NumberOfDFGNodes << "\n";
    region_info_latex.close();

  }


    virtual bool RegionAnalysis (Region *R) {
      if (R->getExit()) { // Check for Exit Block

        std::vector<BasicBlock *> Function_BB_list;
        Function_BB_list.clear();

        Function *F = R->block_begin()->getParent();

        // Gather Block of the function.
        for(Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {

          if(find_bb(Function_BB_list, &*BB) == -1)
            Function_BB_list.push_back(&*BB);

        }

        //errs()<< "BB list size is : "  << Function_BB_list.size() << "\n"; // This was used for Debug!


        // Gather the input Data Flow for the Region.
        int Input = gatherInput(R);

        // Gather the output Data Flow for the Region.
        //
        // We do not consider the whole function as possible Region.
        // So Exit Block should not be NULL. (ExitBlock != NULL)
        int Output = gatherOutput(R);

        // Check if specified I/O Constraints are met.
        //if (Input<= User_Input && Output<=User_Output) {


          //float test_2 = getDelayOfRegion(R); // Test_2 Remove it after you are done!
          
          PrintRegion(R);
          // errs() << " I " << Input << " O " << Output ;
          // int InputData  = getInputData(R);
          // int OutputData = getOutputData(R);
          // errs() << " Func_Freq "  << getEntryCount(R->block_begin()->getParent()); // Function Entry Count Print!
          // errs() << " A " << getAreaofRegion(R) ;// Print Area of the Region
          //getDelayOfRegion(R);
          printBBRegionList(R, Function_BB_list);
          

          // errs() << "     Input   Data is :  " << InputData  << "\n";
          // errs() << "     Output  Data is :  " << OutputData << "\n";

          // Loops Information
          LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
          ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();

          PrintRegionInfo(R);

          unsigned int NumberOfLoops = 0;
          unsigned int NumberOfArrays = 0;

          getNumberOfLoopsandArrays(NumberOfLoops, NumberOfArrays, R, LI, SE);
          errs() << "     Number Of loops  : " << NumberOfLoops   << '\n';
          errs() << "     Number Of Arrays : " << NumberOfArrays  << '\n';

          if (NumberOfLoops) { // Might need to add NumberOfArrays as arguments inside the if statement!

            int InputLoop  = getInputDataLoop(R, LI, SE, NumberOfLoops, NumberOfArrays);
            int OutputLoop = getOutputDataLoop(R, LI, SE, NumberOfLoops);
          }

          // Print Static - Dynamic Classification.
          PrintSDClassification(R, LI, SE);
          errs() << "   **********************************************************************************" << '\n';

        //} // End of if User Input/Outut specified.
      } // End of If Exit Block check.



      return false;



    }


    void gatherRegionsGoodnessAndDensity(Region *R) {



      Region::block_iterator BB = R->block_begin();
      Function   *FunctionOfBB = BB->getParent();


      unsigned int BBRegionCounter = 0;
      unsigned int DFGNodesRegion = 0;
      unsigned int GoodDFGNodesRegion = 0;

      unsigned int   OptimalityRegion = 0;
      float DensityRegion = 0;


      // std::vector<BasicBlock *> BB_list; // Worklist for Basic Blocks in Region.
      // BB_list.clear();

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        runOnBasicBlock(BB, &DFGNodesRegion, &GoodDFGNodesRegion, &OptimalityRegion);

      }

      DensityRegion = OptimalityRegion / DFGNodesRegion; // Density of the Region.


      errs() << "   -------------------------------------------------------------" << '\n';
      errs() << "\n     BB Number is              : " << BBRegionCounter << "\n";
      errs() << "     Good DFG Nodes are        : " << GoodDFGNodesRegion << "\n" ; 
      errs() << "     DFG Nodes Number is       : " << DFGNodesRegion << "\n\n";
      errs() << "     Optimality of Region is   : " << OptimalityRegion << "\n";
      errs() << "     Density of Region is      : " << DensityRegion << "\n\n";
      errs() << "   -------------------------------------------------------------" << '\n';
   
      errs() << "Good " << OptimalityRegion << " Dens " << static_cast<int>(DensityRegion) << " Func " << \
        FunctionOfBB->getName() << " Reg " << R->getNameStr() ;
    }



    // Get the Delay Estimation for the Region.
    //
    //
    float getDelayOfRegionPerIter(Region *R) {

      float DelayOfRegion, DelayOfRegionTotal = 0;
      BlockFrequencyInfo *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI(); 
      std::vector<BasicBlock *> worklist, predecessor_bb, successor_bb;
      std::vector<float> BBFreqPerIter;
      std::vector<float> BBFreqTotal;
      std::vector<float> DelayRegionPathsPerIter, DelayRegionPathsTotal;

      // Clear vectors.
      worklist.clear();
      predecessor_bb.clear();
      successor_bb.clear();
      BBFreqPerIter.clear();
      BBFreqTotal.clear();
      DelayRegionPathsPerIter.clear();
      DelayRegionPathsTotal.clear();

      // Populate worklist with Region's Basic Blocks and their respective BB's Frequencies. Both Per Iteration and Total.
      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        float BBFreqFloat = static_cast<float>(static_cast<float>(BFI->getBlockFreq(*BB).getFrequency()) / static_cast<float>(BFI->getEntryFreq()));
        int EntryFuncFreq = getEntryCount(R->block_begin()->getParent());
        float BBFreq = BBFreqFloat * static_cast<float>(EntryFuncFreq);
        
        worklist.push_back(*BB);
        BBFreqPerIter.push_back(BBFreqFloat);
        BBFreqTotal.push_back(BBFreq);
      }

      // errs() << "\n";
      // for (int i=0; i< worklist.size(); i++) {
      //   errs() << " BBs in Region " << worklist[i]->getName() << " Freq per Iter " << BBFreqPerIter[i] <<  
      //     " Freq Total " << BBFreqTotal[i] << "\n"; // My debugging Info!    
      // }

      // Region has more than one BBs.
      if (worklist.size() > 1) {

        // Find Relations among BBs.
        //
        // Predecessor --> Successor
        //
        //
        int count =0;  
        
        for (std::vector<BasicBlock *>::iterator bb_iter = worklist.begin(); bb_iter != worklist.end(); ++bb_iter, count++) {

          if(BasicBlock *BB = *bb_iter) {
            // Getting the Succeror BBs of each BB in the worklist.
            for (succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) { 
              
              BasicBlock *Succ = *SI;      
      
              if(count < find_bb(worklist, Succ) ) { 

                predecessor_bb.push_back(BB); // Populate send_node vector
                successor_bb.push_back(Succ); // Populate receive_node vector
              }
            }
          }
        }

        // errs() << "\n\n"  ;
        // for (int i=0; i< predecessor_bb.size(); i++) {
        //   errs() << " BB Edges in the Region : " << predecessor_bb[i]->getName() << "  --->     " <<  successor_bb[i]->getName() << "\n"; // My debugging Info!
        // }



        // Critical Path Estimation. 
        //       
        // 
        for (std::vector<BasicBlock *>::iterator bb_iter = worklist.begin(); bb_iter != worklist.end(); ++bb_iter) {

          BasicBlock *BB = *bb_iter;

          // Find the end Nodes - Bottom-most Nodes (BBs) in the CFG Graph.
          if (find_bb(predecessor_bb, BB) == -1) {

            BasicBlock *EndNode = BB;

            BasicBlock *CurrentNode;
            int position;
            float delay_path_estimation, delay_path_estimation_total;

            while(find_bb(successor_bb, EndNode)>=0) {  

              CurrentNode = EndNode;
              position= 0;
              delay_path_estimation= getDelayOfBB(CurrentNode) * BBFreqPerIter[find_bb(worklist, CurrentNode)];
              delay_path_estimation_total = getDelayOfBB(CurrentNode) * BBFreqTotal[find_bb(worklist, CurrentNode)];

              while (find_bb(successor_bb, CurrentNode) >=0) {

                position = find_bb(successor_bb, CurrentNode); 
                delay_path_estimation = delay_path_estimation + (getDelayOfBB(predecessor_bb[position]) * BBFreqPerIter[find_bb(worklist, predecessor_bb[position])]);
                delay_path_estimation_total = delay_path_estimation_total + (getDelayOfBB(predecessor_bb[position]) * BBFreqTotal[find_bb(worklist, predecessor_bb[position])]);
                CurrentNode = predecessor_bb[position];

                // errs() << "Delay for this node " << format("%.8f", getDelayEstim(send_node[position])) << "\n"; // My debugging Info!    
                // errs() << "Delay path estim    " <<  format("%.8f", delay_path_estimation ) << "\n"; // My debugging Info!
                // errs() << " Current Node is:   " << *CurrentNode << "\n";
              }

              // errs() << "Delay path estim    " <<  format("%.8f", delay_path_estimation ) << "\n"; // My debugging Info!
              DelayRegionPathsPerIter.push_back(delay_path_estimation);
              DelayRegionPathsTotal.push_back(delay_path_estimation_total);
              successor_bb.erase(successor_bb.begin() + position);   // deleting the last edge
              predecessor_bb.erase(predecessor_bb.begin() + position);        //  deleting the last edge

              
            }
          }
        }

        DelayOfRegion = get_max(DelayRegionPathsPerIter);       // Per Iteration.
        DelayOfRegionTotal = get_max(DelayRegionPathsTotal);    // Total Delay.
      }

      // In case that the Region has only one BB.
      // else if (worklist.size() == 1) {
      else {
        DelayOfRegion      = getDelayOfBB(worklist[0]) * BBFreqPerIter[0];
        DelayOfRegionTotal = getDelayOfBB(worklist[0]) * BBFreqTotal[0];
      }

 

      // errs() << " Delay Estimation for Region per Iteration is : " << format("%.8f", DelayOfRegion)      << " nSecs" << "\n";
      // errs() << " Delay Estimation for Region Total         is : " << format("%.8f", DelayOfRegionTotal) << " nSecs" << "\n";

      // errs() << " DEPI " << format("%.8f", DelayOfRegion);
      // errs() << " DET " << format("%.8f", DelayOfRegionTotal) << " ";


      return DelayOfRegion;
    }


    virtual void getNumberOfLoopsandArrays (unsigned int &NumberOfLoops, unsigned int &NumberOfArrays, Region *R, LoopInfo &LI, ScalarEvolution &SE ) {

      std::vector<Loop *> Loops;
      Loops.clear();
      std::vector<Value *> ArrayReferences;
      ArrayReferences.clear();

      // Loops Category
      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        BasicBlock *CurrentBlock = *BB;

        // Iterate inside the Loop.
        if (Loop *L = LI.getLoopFor(CurrentBlock)) {
            errs() << "\n     Num of Back Edges     : " << L->getNumBackEdges() << "\n";
            errs() << "     Loop Depth            : " << L->getLoopDepth() << "\n";
            errs() << "     Backedge Taken Count  : " << *SE.getBackedgeTakenCount(L) << '\n';
            errs() << "     Loop iterations       : " << SE.getSmallConstantTripCount(L) << "\n\n";

            NumberOfArrays += GatherNumberOfArrays(CurrentBlock, ArrayReferences); 

            if (find_loop(Loops, L) == -1 ){ 
                Loops.push_back(L);
                NumberOfLoops++;
              }


        }
      } // End of for

    }
   

    virtual int getInputData(Region *R) {

      int InputData = 0;
      int NumberOfLoads = 0;

    for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {
      BasicBlock *CurrentBlock = *BB;

      // Iterate inside the basic block.
      for(BasicBlock::iterator BI = CurrentBlock->begin(), BE = CurrentBlock->end(); BI != BE; ++BI) {

        //if(Instruction *Inst = dyn_cast<Instruction>(&*BI)) {

         // Do not consider Branch Instructions.
         if (dyn_cast<BranchInst>(&*BI))
          continue;

          // Load Info
          if(LoadInst *Load = dyn_cast<LoadInst>(&*BI)) {

            // Non-Atomic and Non-Volatile Load.
            // if (Load->isSimple())
            //   errs() << "   Simple Load  " << '\n';

            InputData += Load->getType()->getPrimitiveSizeInBits();
            ++NumberOfLoads;


          }


      }
    }

    errs() << " Loads " << NumberOfLoads ;

      return InputData;
    }

    virtual int getInputDataLoop(Region *R, LoopInfo &LI, ScalarEvolution &SE, unsigned int NumberOfLoops, unsigned int NumberOfArrays) {

      int InputData = 0;
      int NumberOfLoads = 0;

      int *LoopIterationsArray   = new int[NumberOfLoops] ();
      std::string *ArrayRefNames = new std::string[NumberOfArrays] ();
      int *ArrayLoads            = new int[NumberOfArrays] ();  // Could use std::vector instead.

      int indexNamesArray = 0;

      std::vector<Value *> ArrayReferences;
      ArrayReferences.clear();

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {
        BasicBlock *CurrentBlock = *BB;
        int BBLoads = 0;
        unsigned int loop_depth =0;

        // Iterate inside the basic block.
        for(BasicBlock::iterator BI = CurrentBlock->begin(), BE = CurrentBlock->end(); BI != BE; ++BI) {

          if (Loop *L = LI.getLoopFor(CurrentBlock)) {
          
            loop_depth = L->getLoopDepth();

            // Check Number Of Loops!
            if (NumberOfLoops>=1) {

              LoopIterationsArray[loop_depth-1] = SE.getSmallConstantTripCount(L);

              // Load Info
              if(LoadInst *Load = dyn_cast<LoadInst>(&*BI)) {

                if (GetElementPtrInst *Source = dyn_cast<GetElementPtrInst>(&*Load->getOperand(0))) {

                  // Load comes from an Array.
                  if (Value *ArrayRef = Source->getPointerOperand()) {

                    std::string ArrayRefName = ArrayRef->getName();

                    if (find_array(ArrayReferences, ArrayRef) == -1) {
                      ArrayReferences.push_back(ArrayRef);
                      ArrayRefNames[indexNamesArray]=ArrayRefName;
                      indexNamesArray++;
                    }

                    for (unsigned int i=0; i<NumberOfArrays; i++)
                      if (ArrayRefName == ArrayRefNames[i])
                        ArrayLoads[i]++;


                  } // End of Array check.
                }



              int InputLoad = Load->getType()->getPrimitiveSizeInBits();

              if (NumberOfLoops==1)
                InputLoad = InputLoad * LoopIterationsArray[loop_depth-1];
              
              else
                for (unsigned int i=0; i<loop_depth; i++)
                  InputLoad = InputLoad * LoopIterationsArray[i];
              

                  

                InputData +=InputLoad;
                ++NumberOfLoads;
                ++BBLoads;


              }
            }           
          }
        }

        if (BBLoads && NumberOfArrays) {

          // Print for Total Loads in a Basic Block.
          errs() << "     Input Data for " << CurrentBlock->getName() << " is   :  " << BBLoads ;  
          if (NumberOfLoops>1) {
            for (unsigned int j=0; j<loop_depth; j++)
              errs() << " X "  << LoopIterationsArray[j];
          }

          else
            errs() << " X "  << LoopIterationsArray[loop_depth-1];
        
          errs() << "\n\n";

          // Print for each Array separately.
          if (NumberOfLoops>=1) {
            for (unsigned int i=0; i<NumberOfArrays; i++) {

              if (ArrayLoads[i]) {
                errs() << "     Input Data for Array "<< ArrayRefNames[i] << "  is   :  " << ArrayLoads[i];

                if (NumberOfLoops==1)
                  errs() << " X "  << LoopIterationsArray[loop_depth-1];

                else
                  for (unsigned int j=0; j<loop_depth; j++)
                    errs() << " X "  << LoopIterationsArray[j];
              

                errs() << "\n";
              } 
            }           
          }        
          errs() << "\n\n";
        }
      }

      errs() << "     Loads                  :  " << NumberOfLoads << '\n';
      errs() << "     Input Data is (Bytes)  :  " << InputData / 8 << "\n\n";

      // Clean Up.
      delete [] LoopIterationsArray;
      delete [] ArrayRefNames;
      delete [] ArrayLoads;

      return InputData;
    }

     virtual int getOutputData(Region *R) {

      int OutputData = 0;
      int NumberOfStores = 0;

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {
        BasicBlock *CurrentBlock = *BB;

        // Iterate inside the basic block.
        for(BasicBlock::iterator BI = CurrentBlock->begin(), BE = CurrentBlock->end(); BI != BE; ++BI) {

          ///if(Instruction *Inst = dyn_cast<Instruction>(&*BI)) {

           // Do not consider Branch Instructions.
           if (dyn_cast<BranchInst>(&*BI))
            continue;

            // Store Info
            if(StoreInst *Store = dyn_cast<StoreInst>(&*BI)) {

              OutputData += Store->getOperand(0)->getType()->getPrimitiveSizeInBits();
              ++NumberOfStores;

            }

        }
      }

      errs() << " Stores " << NumberOfStores  ;
  

      return OutputData;
    }

    virtual int getOutputDataLoop(Region *R, LoopInfo &LI, ScalarEvolution &SE, unsigned int NumberOfLoops) {

      int OutputData = 0;
      int NumberOfStores = 0;
      int LoopIterationsArray[10]= {0};
      // std::vector<Loop *> Loops;
      // Loops.clear();

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {
        BasicBlock *CurrentBlock = *BB;

        // Iterate inside the basic block.
        for(BasicBlock::iterator BI = CurrentBlock->begin(), BE = CurrentBlock->end(); BI != BE; ++BI) {

          if (Loop *L = LI.getLoopFor(CurrentBlock)) {
          
            unsigned int loop_depth = L->getLoopDepth();

            // Check Number Of Loops!
            if (NumberOfLoops>1) {

              LoopIterationsArray[loop_depth-1] = SE.getSmallConstantTripCount(L);

              // Load Info
              if(StoreInst *Store = dyn_cast<StoreInst>(&*BI)) {

              int OutputStore = Store->getOperand(0)->getType()->getPrimitiveSizeInBits();

              for (unsigned int i=0; i<loop_depth; i++)
                OutputStore = OutputStore * LoopIterationsArray[i];
                  

                OutputData +=OutputStore;
                ++NumberOfStores;


              }
            }
            
            else {

              LoopIterationsArray[0] = SE.getSmallConstantTripCount(L);  
              
              // Load Info
              if(StoreInst *Store = dyn_cast<StoreInst>(&*BI)) {

              int OutputStore = Store->getOperand(0)->getType()->getPrimitiveSizeInBits();

              OutputStore = OutputStore * LoopIterationsArray[0];
                  
              OutputData +=OutputStore;
              ++NumberOfStores;


              }
            }

          }

        }
      }

      errs() << "     Stores                  :  " << NumberOfStores << '\n';
      errs() << "     Output Data is (Bytes)  :  " << OutputData / 8 << "\n\n";

      return OutputData;
    }


    // @brief  Gather Output Data Flow for the region.
    //
    // @param  R    The Region for which we are gathering information.
    //
    // @return int  The number of output Data instances (instructions) of the Region.
    virtual int gatherOutput(Region *R) {

      auto *TLIP = getAnalysisIfAvailable<TargetLibraryInfoWrapperPass>();
      TargetLibraryInfo *TLI = TLIP ? &TLIP->getTLI() : nullptr;
      int Output_number = 0;
      std::vector<Instruction *> ext_out; // Worklist for external output instructions.
      ext_out.clear();

      // Iterate over the Region's Basic Blocks.
      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        // Iterate inside the basic block.
        for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

          if(Instruction *Inst = dyn_cast<Instruction>(&*BI)) {

            // Do not consider Branch Instructions.
            if (dyn_cast<BranchInst>(&*BI))
              continue;

            if (!isInstructionTriviallyDead(Inst, TLI)) {      

              // Get the Users of the instruction.
              for (User *U : Inst->users()) {

                
        
                if (Instruction *User_Inst = dyn_cast<Instruction>(U)) {

                  // If the User is not inside this Region then it is considered as output. 
                  if (!(R->contains(User_Inst))) {

                    if (Inst && find_inst(ext_out, Inst) == -1) {
                      ext_out.push_back(Inst);
                      ++Output_number;
                      //errs()<< "    Output Instruction : " << "\t" << Inst->getName() << "\n";
                    }
                  }
                }
              }
            }
          }
        }
      }

      //errs() << "\n   Output Alive Number is  : " << Output_number << "\n\n";
      return Output_number;           
    }


    // @brief  Gather Input Data Flow for the region.
    //
    // @param  R    The Region for which we are gathering information.
    //
    // @return int  The number of Input Data instances (instructions) of the Region.
    virtual int gatherInput(Region *R) {

      auto *TLIP = getAnalysisIfAvailable<TargetLibraryInfoWrapperPass>();
      TargetLibraryInfo *TLI = TLIP ? &TLIP->getTLI() : nullptr;
      int Input_number  = 0;
      std::vector<Value *> ext_in;
      ext_in.clear();

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        // Iterate inside the basic block.
        for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

          if(Instruction *Inst = dyn_cast<Instruction>(&*BI)) {

            // Do not consider Branch Instructions.
            if (dyn_cast<BranchInst>(&*BI))
              continue;

            if (!isInstructionTriviallyDead(Inst, TLI)) {      

              // Iterate over each operand of each Instruction.
              for (unsigned int i=0; i<Inst->getNumOperands(); i++) {

                Value *Operand = Inst->getOperand(i);

                // Exclude operands that represent constants.(signed integers) 
                if (Inst->getOperand(i)->getValueID() == 11)
                  continue; 

                // Iterate over all the instructions of the Region and compare the operand to them.
                bool local = compareInstrToOperand(R, Inst->getOperand(i));

                // Data Flow is incremented if the operand is not coming from a local Instruction.
                if (!local && Operand) {

                  if (find_op(ext_in, Operand) == -1) {
                    ext_in.push_back(Operand);
                    ++Input_number;
                    //errs()<< "     Input Operand : " << "\t" << Inst->getOperand(i)->getName() << "\n";
                  }
                }
              }
            }
          }
        }
      }

      //errs() << "\n   Input  Alive Number is  : " << Input_number << "\n\n"; 
      
      DEBUG(errs() << "I am here!\n");
      return Input_number;
    }

    // @brief  Compare Instructions of Basic Block to Operand.
    //
    // If the operand of a BB is not coming from a local instruction
    // of the same BB, then it is being received by a predecessor BB. 
    //
    // @param @param  R  The Region for which we are gathering information.
    //        Value The  Operand that we are comparing.
    //        int   The  Data Flow Number that represents either the
    //              input or the output value for the Region. 
    //
    // @return void
    virtual bool compareInstrToOperand(Region *R, Value *Operand) {

      bool local = false;

      for(Region::block_iterator BB = R->block_begin(), E = R->block_end(); BB != E; ++BB) {

        // Iterate inside the basic block.
        for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

          if(Instruction *Inst = dyn_cast<Instruction>(&*BI)) {

            // Do not consider Branch Instructions.
            if (dyn_cast<BranchInst>(&*BI))
              continue;

            // Compare Operand with Instructions in BB.   
            // if (Operand->getName() != "") {
            //   if (Operand->getName() == Inst->getName())
            //     local = true;
            // }
            
            else
              if (Operand)
                if (Operand == Inst)
                  local = true;
          }
        }
      }

      return local;

    }

    virtual unsigned int GatherNumberOfArrays(BasicBlock *BB, std::vector<Value *> ArrayReferences) {

      unsigned int NumberOfArrays = 0;

      // Iterate inside the basic block.
      for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

        // Load Info
        if(LoadInst *Load = dyn_cast<LoadInst>(&*BI)) {

          if (GetElementPtrInst *Source = dyn_cast<GetElementPtrInst>(&*Load->getOperand(0))) {

            // Load comes from an Array.
            if (Value *ArrayRef = Source->getPointerOperand()) {

              if (find_array(ArrayReferences, ArrayRef) == -1) {
                ArrayReferences.push_back(ArrayRef);
                NumberOfArrays++;
              }


            } // End of Array check.
          }
        }
      }

      
      return NumberOfArrays;
    }

    int getEntryCount(Function *F) {

      int entry_freq = 0;

      if (F->hasMetadata()) {

        MDNode *node = F->getMetadata("prof");

        if (MDString::classof(node->getOperand(0))) {
          auto mds = cast<MDString>(node->getOperand(0));
          std::string metadata_str = mds->getString();

          if (metadata_str == "function_entry_count"){
            if (ConstantInt *CI = mdconst::dyn_extract<ConstantInt>(node->getOperand(1))) {
              entry_freq = CI->getSExtValue();
              //errs() <<" Func_Freq " << entry_freq << " "; //  Turn it back on mayne.
            }              

          }
        }
      }

      return entry_freq;
    }


    virtual void getAnalysisUsage(AnalysisUsage& AU) const override {
              
        AU.addRequired<LoopInfoWrapperPass>();
        AU.addRequired<RegionInfoPass>();
        AU.addRequired<DependenceAnalysis>();
        AU.addRequiredTransitive<RegionInfoPass>();
        AU.addRequiredTransitive<ScalarEvolutionWrapperPass>();
        AU.addRequired<BlockFrequencyInfoWrapperPass>();
        AU.setPreservesAll();
    } 
  };
}

char IdentifyRegions::ID = 0;
static RegisterPass<IdentifyRegions> X("IdentifyRegions", "Identify Valid Regions");
