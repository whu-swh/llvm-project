//===---- MachineOutliner.h - Outliner data structures ------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Contains all data structures shared between the outliner implemented in
/// MachineOutliner.cpp and target implementations of the outliner.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_MACHINEOUTLINER_SWH_H
#define LLVM_MACHINEOUTLINER_SWH_H

#include "llvm/CodeGen/MachineOutliner.h"
#include "MachineDominators.h"
#include "MachinePostDominators.h"
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/LiveRegUnits.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"

namespace llvm {
namespace outliner {

struct SwhSeseRegion : public Candidate{
  MachineFunction *ParentFunc;
  // blockList::[ beginBlockNum, endBlockNum, internalBlockNum1, ...]
  std::vector<int> BlockList;
  int Tag;
  unsigned AvaliableRegister;
  void sortByBFS(Module &M, MachineFunction &MF);
  void sortByDefault(Module &M, MachineFunction &MF);
  void addSuccessorIntoListByBFS(MachineBasicBlock &Predecessor, MachineBasicBlock &End, std::vector<int> &List);
  void addSuccessorIntoListByDefault(MachineBasicBlock &Predecessor, MachineBasicBlock &End, std::vector<int> &List);
  bool compareWith(SwhSeseRegion ComparedRegion, Module &M, MachineModuleInfo &MMI);
  int compareMBBs(MachineBasicBlock &Mbb1, MachineBasicBlock &Mbb2, MachineModuleInfo &MMI, SwhSeseRegion ComparedRegion);
  int isSameTerminator(MachineInstr &Ti1, MachineInstr &Ti2, SwhSeseRegion ComparedRegion);
  bool listContains(std::vector<int> Vector, int Number) const;
  MachineFunction *
  toMachineFunction(MachineFunction &Function, const TargetSubtargetInfo &Info,
                    const TargetInstrInfo &Info1,
                    const std::vector<MCCFIInstruction> &Vector,
                    bool EndWithPointerToSelf, bool EndWithMoreThanOneTerminator);
  void addRelation(MachineFunction &MF, const TargetSubtargetInfo &TSI,
                   const TargetInstrInfo &TII,
                   const std::vector<MCCFIInstruction> &Instrs, bool EndWithPointerToSelf);
  bool isEndWithPointerToSelf() const;
  bool isEndWithMoreThanOneTerminator() const;
  bool isContainsCall();
  bool isContainsStackOperation();

  MachineFunction *getMF() const { return ParentFunc; }
  void initLRU(const TargetRegisterInfo &TRI);

//  SWH_SESERegion operator=(SWH_SESERegion& rightRegion){
//    //父函数直接拷贝指针
//    parentFunc = rightRegion.parentFunc;
//    tag = rightRegion.tag;
//    AvaliableRegister = rightRegion.AvaliableRegister;
//  }
  bool checkCompleteness();
  bool checkPostCompleteness();
};


struct AbstractedFunction:public OutlinedFunction{
  std::list<SwhSeseRegion> RegionCandidates;

  bool EndWithPointerToSelfRegion = false;
  bool EndWithMoreThanOneTerminator = false;
  bool ContainsCall = false;
  unsigned AbstractingID = 0;
  unsigned RegionSize = 0;
  unsigned AbstractedBenefit = 0;
  unsigned AvaliableRegister = 0;
  unsigned int FrameOverhead;

  MachineBasicBlock *getEndMachineBasicBlock() const{
    //TODO：to fix the end MBB
    return MF->getBlockNumbered(1);
  }
  MachineBasicBlock *getStartMachineBasicBlock() const{
    //TODO：to fix the end MBB
    return MF->getBlockNumbered(0);
  }

  /// Return the number of candidates for this \p OutlinedFunction.
  unsigned getOccurrenceCount() const { return RegionCandidates.size(); }
  /// Return the number of instructions in this sequence.
  unsigned getNumInstrs() const {
    unsigned NumInstrs = 0;
    for (int I :RegionCandidates.begin()->BlockList) {
      NumInstrs += RegionCandidates.begin()->ParentFunc->getBlockNumbered(I)->size();
    }
    return NumInstrs;
  }

  /// Return the size in bytes of the unoutlined sequences.
  unsigned getNotAbstractedCost() const {
    return getOccurrenceCount() * RegionSize;
  }
  /// Return the number of bytes it would take to outline this
  /// function.
  unsigned getAbstractingCost() const {
    unsigned CallOverhead = 0;
    for (const SwhSeseRegion &C : RegionCandidates)
      CallOverhead += C.getCallOverhead();
    return CallOverhead + RegionSize + FrameOverhead;
  }


  /// Return the number of instructions that would be saved by outlining
  /// this function.
  unsigned getAbstractedBenefit() const {
    unsigned NotAbstractedCost = getNotAbstractedCost();
    unsigned AbstractedCost = getAbstractingCost();
    return (NotAbstractedCost < AbstractedCost) ? 0
                                            : NotAbstractedCost - AbstractedCost;
  }

  void emitMark();

  void reinitAF(unsigned AID,
                unsigned AvaRegister, unsigned RSize, unsigned FOverhead){
    AbstractingID = AID;
    AvaliableRegister = AvaRegister;
    RegionSize = RSize;
    FrameOverhead = FOverhead;

    AbstractedBenefit = getAbstractedBenefit();
    if (AbstractingID>0) ContainsCall= true;
    EndWithPointerToSelfRegion =
        RegionCandidates.begin()->isEndWithPointerToSelf();
    EndWithMoreThanOneTerminator = RegionCandidates.begin()->isEndWithMoreThanOneTerminator();
    if(AbstractingID == 0){
      AbstractingID++;
    }
  }

  AbstractedFunction(std::list<SwhSeseRegion> &RegionCandidates, unsigned AbstractingID,
                     unsigned AvaliableRegister, unsigned RegionSize, unsigned FrameOverHead)
        :RegionCandidates(RegionCandidates), AbstractingID(AbstractingID),
         RegionSize(RegionSize), AvaliableRegister(AvaliableRegister),FrameOverhead(FrameOverHead){
    AbstractedBenefit = getAbstractedBenefit();
    if (AbstractingID>0) ContainsCall= true;
    EndWithPointerToSelfRegion =
        RegionCandidates.begin()->isEndWithPointerToSelf();
    EndWithMoreThanOneTerminator = RegionCandidates.begin()->isEndWithMoreThanOneTerminator();
    if(AbstractingID == 0){
      AbstractingID++;
    }
  }
  AbstractedFunction(std::list<SwhSeseRegion> &RegionCandidates)
      :RegionCandidates(RegionCandidates){

  }

  AbstractedFunction(){
    AbstractingID = 3;
  }


};

struct SwhFingerprintConstructor {
  uint64_t Fingerprint =0;
  uint64_t BlockCount;
  uint64_t InstructionCount;
  int Buoy = 8;
  void addBlockPart(uint64_t BlockType,uint64_t InstrCountInBlock) {
    if (Buoy>0){
      BlockType &= 0x3;
      if (InstrCountInBlock>0xF)
        InstrCountInBlock = 0xF;
      else
        InstrCountInBlock &= 0xF;
      Fingerprint |= (BlockType<<(6*Buoy-2))|(InstrCountInBlock<<(6*Buoy-6));
      Buoy--;
    }
  }
  void addRegionPart(uint64_t BlockCount,uint64_t InstrCount){
    if (BlockCount>0xFF)
      BlockCount=0xFF;
    if (InstrCount>0xFF)
      InstrCount=0xFF;
    Fingerprint |= (BlockCount<<56)|(InstrCount<<48);
  }

  bool operator < (const SwhFingerprintConstructor X) const {
    return Fingerprint < X.Fingerprint;      //从小到大排序
  }

};

struct SwhNeededRegionsInfo{
//  std::map<SWH_FingerprintConstructor,std::vector<SWH_SESERegion>> regionsWithFP;
  std::map<uint64_t, std::list<SwhSeseRegion>> RegionsWithFp;
  std::map<int, AbstractedFunction> RegionsWithTag;
};

struct SwhNeededMfInfo {

  std::vector<std::vector<int>> DominateMatrix;
  std::vector<std::vector<int>> PostDominateMatrix;
  std::vector<std::vector<int>> BiDirectionalDominateMatrix;

  void swhGetNeededRegionsInfo(MachineFunction &MF, SwhNeededRegionsInfo &NeededRegionsInfo);

  void swhGetBiDirectionalDominateMatrix(MachineFunction &MF, MachineDominatorTree &MDT, MachinePostDominatorTree &MPDT, std::vector<std::vector<int>> &Matrix0);
  void swhGetDominateMatrix(MachineFunction &MF, MachineDominatorTree &MDT, std::vector<std::vector<int>> &Matrix0);
  void swhGetPostDominateMatrix(MachineFunction &MF, MachinePostDominatorTree &MPDT, std::vector<std::vector<int>> &Matrix0);
  void swhGetMatrixAnd(std::vector<std::vector<int>> Matrix1,
                   std::vector<std::vector<int>> Matrix2, std::vector<std::vector<int>> &Matrix0);

//  ~SWH_NeededMFInfo(){
//    for(int i=0; i<dominateMatrix.size(); i++){
//      dominateMatrix[i].clear();
////      dominateMatrix[i].~vector();
//    }
//    dominateMatrix.clear();
//    dominateMatrix.~vector();
//
//    for(int i=0; i<postDominateMatrix.size(); i++){
//      postDominateMatrix[i].clear();
////      postDominateMatrix[i].~vector();
//    }
//    postDominateMatrix.clear();
//    postDominateMatrix.~vector();
//
//    for(int i=0; i<biDirectionalDominateMatrix.size(); i++){
//      biDirectionalDominateMatrix[i].clear();
////      biDirectionalDominateMatrix[i].~vector();
//    }
//    biDirectionalDominateMatrix.clear();
//    biDirectionalDominateMatrix.~vector();
//  }
};

struct SwhCrossBasicBlockOpt{
  Module *M;
  MachineModuleInfo *MMI;
  //used to remove duplicate
  //用一个pair的set来查重
  std::set<std::pair<MachineFunction *, int>> AbstractedBlocks;

  std::map<StringRef, SwhNeededMfInfo *> NeededMfInfoMap;
  SwhNeededRegionsInfo NeededRegionsInfo;
//  std::map<MachineInstr, int> instrFrequency;
  unsigned FunctionsCreated = 0;


  void swhPrepareNecessaryInfo(Module &M0, MachineModuleInfo &MMI0);
  void swhCompareRegionsWithFingerprintting();
  void swhDoAbstract();
  MachineFunction *swhCreateAbstractFunction(unsigned Name,
                                              AbstractedFunction &AF);

  DISubprogram *swhGetSubprogramOrNull(const AbstractedFunction &AF);
  void swhPrepareForAbstract();
  bool haveAbstractedPartOf(AbstractedFunction &AF);
  void testNewFunc(int A);
};



} // namespace outliner
} // namespace llvm

#endif
