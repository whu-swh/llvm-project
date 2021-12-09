#include "llvm/CodeGen/MachineOutlinerSWH.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Twine.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineOptimizationRemarkEmitter.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Mangler.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include <iterator>
#include <llvm/Support/GraphWriter.h>
#include "llvm/Support/SuffixTree.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>
#include <tuple>
#include <vector>

#define DEBUG_TYPE "machine-outliner-swh"

using namespace llvm;
using namespace ore;
using namespace outliner;

STATISTIC(NumOutlined_swh, "Number of candidates outlined");
STATISTIC(FunctionsCreated_swh, "Number of functions created");

// Set to true if the user wants the outliner to run on linkonceodr linkage
// functions. This is false by default because the linker can dedupe linkonceodr
// functions. Since the outliner is confined to a single module (modulo LTO),
// this is off by default. It should, however, be the default behaviour in
// LTO.
// static cl::opt<bool> EnableLinkOnceODROutlining(
//     "enable-linkonceodr-outlining", cl::Hidden,
//     cl::desc("Enable the machine outliner on linkonceodr functions"),
//     cl::init(false));

/// Number of times to re-run the outliner. This is not the total number of runs
/// as the outliner will run at least one time. The default value is set to 0,
/// meaning the outliner will run one time and rerun zero times after that.
// static cl::opt<unsigned> OutlinerReruns(
    // "machine-outliner-reruns", cl::init(0), cl::Hidden,
    // cl::desc(
    //     "Number of times to rerun the outliner after the initial outline"));namespace llvm{

namespace llvm{
namespace outliner {

//region RegionCandidate SESERegion


///return : -1 not equal; 0 conditional equal; 1 equal.
int SwhSeseRegion::compareMBBs(MachineBasicBlock &Mbb1, MachineBasicBlock &Mbb2,MachineModuleInfo &MMI, SwhSeseRegion ComparedRegion){
  if (Mbb1.size() != Mbb2.size())
    return -1;
  MachineBasicBlock::iterator It1 = Mbb1.begin();
  MachineBasicBlock::iterator It2 = Mbb2.begin();
  for (MachineBasicBlock::iterator Et1 =Mbb1.end(); It1!=Et1; ++It1, ++It2) {
    MachineInstr *Mi1 = &(*It1);
    MachineInstr *Mi2 = &(*It2);
    if (!MachineInstrExpressionTrait::isEqual(Mi1,Mi2)){
      //如果不完全相等
      if(Mi1->isTerminator() && Mi2->isTerminator()){
        //判断是否是相同的terminator
        //因为考虑到目标参数不同
        return isSameTerminator(*Mi1, *Mi2, ComparedRegion);
      }
      //当Terminator中存在间接跳转，且指令不同时，也认为不相等
      //not equal
      return -1;
    }
  }
  //equal
  return 1;
}

bool SwhSeseRegion::compareWith(SwhSeseRegion ComparedRegion, Module &M, MachineModuleInfo &MMI) {
  MachineFunction *MF1 = ParentFunc;
  MachineFunction *MF2 = ComparedRegion.ParentFunc;

  sortByDefault(M,*MF1);
  //在比较前，定SESERegion中BlockList的顺序
  ComparedRegion.sortByDefault(M, *MF2);

  for (unsigned I = 0; I < 2; ++I) {
    MachineBasicBlock *MBB1 = MF1->getBlockNumbered(BlockList[I]);
    MachineBasicBlock *MBB2 = MF2->getBlockNumbered(ComparedRegion.BlockList[I]);
    if (compareMBBs(*MBB1,*MBB2, MMI, ComparedRegion)==-1){
      return false;
    }
  }

  for (unsigned I = 0; I < BlockList.size(); ++I) {
    MachineBasicBlock *MBB1 = MF1->getBlockNumbered(BlockList[I]);
    MachineBasicBlock *MBB2 = MF2->getBlockNumbered(ComparedRegion.BlockList[I]);
    if (compareMBBs(*MBB1,*MBB2, MMI, ComparedRegion)==-1){
      return false;
    }
  }

  return true;
}

void SwhSeseRegion::sortByDefault(Module &M, MachineFunction &MF) {
  //宽度优先搜索顺序，同级节点，按照successor顺序来排序
  std::vector<int> BlockListByBfs;
  MachineBasicBlock *Start = MF.getBlockNumbered(BlockList[0]);
  MachineBasicBlock *End = MF.getBlockNumbered(BlockList[1]);
  BlockListByBfs.push_back(Start->getNumber());
  BlockListByBfs.push_back(End->getNumber());
  addSuccessorIntoListByDefault(*Start, *End, BlockListByBfs);

  for (unsigned I = 2; I < BlockListByBfs.size(); ++I) {
    if (BlockList[I]!=BlockListByBfs[I])
      BlockList[I]=BlockListByBfs[I];
  }
}

void SwhSeseRegion::addSuccessorIntoListByDefault(MachineBasicBlock &Predecessor, MachineBasicBlock &End,std::vector<int> &List) {
  int StartIndex = List.size();
  int EndBlockNum = End.getNumber();

  for (MachineBasicBlock *Succ:Predecessor.successors()) {
    if (Succ->getNumber()!=EndBlockNum && !listContains(List, Succ->getNumber())){
      List.push_back(Succ->getNumber());
    }
  }
  int Endsize = List.size();
  for (int I = StartIndex; I < Endsize; ++I) {
    addSuccessorIntoListByBFS(*Predecessor.getParent()->getBlockNumbered(List[I]),End,List);
  }
}

void SwhSeseRegion::sortByBFS(Module &M, MachineFunction &MF) {
  //宽度优先搜索顺序，同级节点，优先考虑fallthrough节点，然后按照terminator中指定的顺序来排序
  std::vector<int> BlockListByBfs;
  MachineBasicBlock *Start = MF.getBlockNumbered(BlockList[0]);
  MachineBasicBlock *End = MF.getBlockNumbered(BlockList[1]);
  BlockListByBfs.push_back(Start->getNumber());
  BlockListByBfs.push_back(End->getNumber());
  addSuccessorIntoListByBFS(*Start, *End, BlockListByBfs);

  for (unsigned I = 2; I < BlockListByBfs.size(); ++I) {
    if (BlockList[I]!=BlockListByBfs[I])
      BlockList[I]=BlockListByBfs[I];
  }
}

void SwhSeseRegion::addSuccessorIntoListByBFS(MachineBasicBlock &Predecessor, MachineBasicBlock &End, std::vector<int> &List){
  int StartIndex = List.size();
  int EndBlockNum = End.getNumber();
  MachineBasicBlock::iterator MBBI = Predecessor.getFirstTerminator();
  if (Predecessor.canFallThrough()){
    MachineBasicBlock &Succ0 = *Predecessor.getFallThrough();
    if (Succ0.getNumber()!=EndBlockNum && !listContains(List, Succ0.getNumber())){
      List.push_back(Succ0.getNumber());
    }
  }
  while(MBBI!=Predecessor.end()){
    unsigned OprNum = MBBI->getNumOperands();
    for (unsigned I = 0; I < OprNum; ++I) {
      MachineOperand Mo = MBBI->getOperand(I);
      if (Mo.isMBB()){
        MachineBasicBlock *Mbb= Mo.getMBB();
        if (Mbb->getNumber()!=EndBlockNum && !listContains(List, Mbb->getNumber()))
          List.push_back(Mo.getMBB()->getNumber());
      }
    }
    MBBI++;
  }

  int Endsize = List.size();
  for (int I = StartIndex; I < Endsize; ++I) {
    addSuccessorIntoListByBFS(*Predecessor.getParent()->getBlockNumbered(List[I]),End,List);
  }
}

int SwhSeseRegion::isSameTerminator(MachineInstr &Ti1,MachineInstr &Ti2, SwhSeseRegion ComparedRegion) {
  // 若必须操作码不同，视为指令不同
  if (Ti1.getOpcode()!=Ti2.getOpcode())return -1;
  // 若必须操作数个数不同，视为指令不同
  if (Ti1.getNumOperands()!=Ti2.getNumOperands())return -1;
  for (unsigned I = 0; I < Ti1.getNumOperands(); ++I) {
    MachineOperand MO1 = Ti1.getOperand(I);
    MachineOperand MO2 = Ti2.getOperand(I);

    if (hash_value(MO1) != hash_value(MO2)){
      // 若操作数不同，但是操作数是MBB，且在不同block中相互对应，则视为相同
      if (MO1.isMBB()&&MO2.isMBB()){
        std::vector<int>::iterator It1 = std::find(BlockList.begin(),BlockList.end(), MO1.getMBB()->getNumber());
        int Index1 = std::distance(BlockList.begin(), It1);
        std::vector<int>::iterator It2 = std::find(ComparedRegion.BlockList.begin(), ComparedRegion.BlockList.end(), MO2.getMBB()->getNumber());
        int Index2 = std::distance(ComparedRegion.BlockList.begin(), It2);
        if (Index1!=Index2)
          return -1;
        return 0;
      }

      //若其他情况对应操作数不同，视为不同
      return -1;
    }
  }

  return 0;
}

bool SwhSeseRegion::listContains(std::vector<int> Vector, int Number) const {
  return std::find(Vector.begin(), Vector.end(), Number)!=Vector.end();
}

//region Functions for converting region to Machine Func
MachineFunction *SwhSeseRegion::toMachineFunction(
    MachineFunction &Function, const TargetSubtargetInfo &Info,
    const TargetInstrInfo &Info1, const std::vector<MCCFIInstruction> &Vector,
    bool EndWithPointerToSelf, bool EndWithMoreThanOneTerminator) {

  /**
   * TODO: 考虑到llvm的实现，只需要从小到大即可，下面的思路暂不考虑
   * 假设，不存在region内部块会fallthrough到入口块
   * 基于上述假设，我们从入口块开始创建新的function，并沿着fallthrough块遍历region内的块，
   * 直到遍历完region内的所有块；
   * 特殊情况：如果不存在fallthrough的块，那么则从剩余的没有被fallthrough的块开始
   */
  /*
  int blockIndexToCreate = blockList[0];
  for (int a = 0; a<blockList.size();a++){
    int i = blockIndexToCreate;
    // MachineBasicBlock &MBB = *function.CreateMachineBasicBlock();
    // function.insert(function.end(), &MBB);
    MachineBasicBlock *sourceBlcok = parentFunc->getBlockNumbered(blockIndexToCreate);
    if (sourceBlcok->canFallThrough())
    {
      //考虑到endblock以外，其他block不会fallthrough到region外的块
      blockIndexToCreate = sourceBlcok->getFallThrough()->getNumber();
    }
  }
  */
  std::vector<int> BlockListVia = BlockList;
  int StartBlockNum = BlockListVia[0];
  int EndblockNum = BlockListVia[1];
  std::sort(BlockListVia.begin(),BlockListVia.end());
  for (unsigned long A = 0; A < BlockListVia.size(); A++){
    int Via0 = BlockListVia[A];
    MachineBasicBlock &MBB = *Function.CreateMachineBasicBlock();
    // Insert the new function into the module.
    Function.insert(Function.end(), &MBB);
    for (auto I = ParentFunc->getBlockNumbered(Via0)->begin(), E = ParentFunc->getBlockNumbered(Via0)->end(); I != E;
         ++I) {
      if (!EndWithPointerToSelf && Via0==EndblockNum && I==ParentFunc->getBlockNumbered(Via0)->getFirstTerminator()){
        //E==std::next(I)
        // 替换为判断I是不是terminator，如果是，
        //   当endWithPointerToSelf为假时，
        //   应该直接将terminator放在外面，
        //   因此直接结束当前循环
        break;
      }
      MachineInstr *NewMI = Function.CloneMachineInstr(&*I);

      if (I->isCFIInstruction()) {
        unsigned CFIIndex = NewMI->getOperand(0).getCFIIndex();
        MCCFIInstruction CFI = Vector[CFIIndex];
        (void)Function.addFrameInst(CFI);
      }
      NewMI->dropMemRefs(Function);

      // Don't keep debug information for outlined instructions.
      NewMI->setDebugLoc(DebugLoc());
      MBB.insert(MBB.end(), NewMI);
    }
  }
  addRelation(Function, Info, Info1, Vector, EndWithPointerToSelf);

  //当遇到这种特殊情况时,进行修改
  if (BlockListVia[0] != StartBlockNum)
  {
    // parentFunc->print(errs());
    MachineBasicBlock &MBB = *Function.CreateMachineBasicBlock();
    Function.insert(Function.begin(), &MBB);
    auto It = std::find(BlockListVia.begin(), BlockListVia.end(), StartBlockNum);
    int Index = std::distance(BlockListVia.begin(), It);
    MachineBasicBlock *StartMbb = Function.getBlockNumbered(Index);
    Info1.insertUnconditionalBranch(MBB, StartMbb, DebugLoc());
    MBB.addSuccessor(StartMbb);
  }
  return &Function;
}

void SwhSeseRegion::addRelation(MachineFunction &MF,
                                 const TargetSubtargetInfo &TSI,
                                 const TargetInstrInfo &TII,
                                 const std::vector<MCCFIInstruction> &Instrs, bool EndWithPointerToSelf) {
  std::vector<int> BlockListVia = BlockList;
  // int StartBlockNum = BlockListVia[0];
  int EndblockNum = BlockListVia[1];
  std::sort(BlockListVia.begin(),BlockListVia.end());
  for (unsigned I = 0; I < BlockListVia.size(); ++I) {
    MachineBasicBlock *Origin = ParentFunc->getBlockNumbered(BlockListVia[I]);
    MachineBasicBlock *NewMbb = MF.getBlockNumbered(I);
    if (BlockListVia[I] == EndblockNum){
      //for the end block

      if (!EndWithPointerToSelf)
        continue;
      for (MachineBasicBlock *Succ: Origin->successors()){
        if (listContains(BlockListVia, Succ->getNumber())){
          std::vector<int>::iterator It1 = std::find(BlockListVia.begin(),BlockListVia.end(), Succ->getNumber());
          unsigned Index1 = std::distance(BlockListVia.begin(), It1);
          MachineBasicBlock *NewSucc = MF.getBlockNumbered(Index1);
          NewMbb->addSuccessor(NewSucc);

//          MachineBasicBlock::iterator MBBI = newMBB->getFirstTerminator();
          for (MachineBasicBlock::iterator MBBI:NewMbb->terminators()) {
            unsigned OprNum = MBBI->getNumOperands();
            for (unsigned Index2 = 0; Index2 < OprNum; ++Index2) {
              MachineOperand &MO = MBBI->getOperand(Index2);
              if (MO.isMBB() && MO.getMBB() == Succ) {
                MO.setMBB(NewSucc);
              }
            }
          }

        }
      }
      continue;
    }
    for (MachineBasicBlock *Succ: Origin->successors()){
      std::vector<int>::iterator It1 = std::find(BlockListVia.begin(),BlockListVia.end(), Succ->getNumber());
      unsigned Index1 = std::distance(BlockListVia.begin(), It1);
      NewMbb->addSuccessor(MF.getBlockNumbered(Index1));
      if (Origin->getFallThrough() == Succ){
        continue;
      }
//      MachineBasicBlock::iterator MBBI = newMBB->getFirstTerminator();
      for (MachineBasicBlock::iterator MBBI:NewMbb->terminators()) {
        unsigned OprNum = MBBI->getNumOperands();
        for (unsigned Index2 = 0; Index2 < OprNum; ++Index2) {
          MachineOperand &MO = MBBI->getOperand(Index2);
          if (MO.isMBB() && MO.getMBB()==Succ){
            MO.setMBB(MF.getBlockNumbered(Index1));
          }
        }
      }

    }

  }
}
//endregion


bool SwhSeseRegion::isEndWithPointerToSelf() const {
  MachineBasicBlock *EndMbb = ParentFunc->getBlockNumbered(BlockList[1]);

  //利用successor进行检查
  bool HaveInRegionSucc = false;
  for (MachineBasicBlock *MBB:EndMbb->successors()){
    if (listContains(BlockList, MBB->getNumber()))
      HaveInRegionSucc = true;
  }

  //利用end Instr进行检查


  for (MachineBasicBlock::iterator It:EndMbb->terminators()) {
    MachineInstr &EndInstr = *It;
    if (!EndInstr.isTerminator())
      return false;
    for (unsigned I = 0; I < EndInstr.getNumOperands(); ++I) {
      MachineOperand MO = EndInstr.getOperand(I);
      if (MO.isMBB()){
        if (listContains(BlockList,MO.getMBB()->getNumber())){
          //当且仅当，最后一条指令包含指向Region内的MBB的操作数，且有region内的successor时，返回真；
          return HaveInRegionSucc;
        }
      }
    }
  }
  return false;
}

bool SwhSeseRegion::isContainsCall() {
  for (MachineBasicBlock &MBB :*ParentFunc){
    for (MachineInstr &MI :MBB) {
      if (MI.isCall()){
        return true;
      }
    }
  }
  return false;
}

//endregion

DISubprogram * SwhCrossBasicBlockOpt::swhGetSubprogramOrNull(const AbstractedFunction &AF)  {
  for (const SwhSeseRegion &C : AF.RegionCandidates)
    if (MachineFunction *MF = C.ParentFunc)
      if (DISubprogram *SP = MF->getFunction().getSubprogram())
        return SP;
  return nullptr;
}

void SwhNeededMfInfo::swhGetPostDominateMatrix(MachineFunction &MF, MachinePostDominatorTree &MPDT, std::vector<std::vector<int>> &Matrix0) {
  int MFSize = MF.size();
  Matrix0 = std::vector<std::vector<int>>(MFSize,std::vector<int>(MFSize,0));
  for (MachineBasicBlock &Mbbx: MF) {
    for (MachineBasicBlock &Mbby: MF) {
      if (MPDT.dominates(&Mbbx, &Mbby)){
        Matrix0[Mbbx.getNumber()][Mbby.getNumber()]=1;
      }
    }
  }
//  return matrix;
}

void
SwhNeededMfInfo::swhGetBiDirectionalDominateMatrix(MachineFunction &MF, MachineDominatorTree &MDT,
                                                     MachinePostDominatorTree &MPDT, std::vector<std::vector<int>> &Matrix0) {
  swhGetDominateMatrix(MF, MDT, DominateMatrix);
  swhGetPostDominateMatrix(MF, MPDT, PostDominateMatrix);
//  auto bdm = swh_getMatrixAnd(dominateMatrix,postDominateMatrix);
//  biDirectionalDominateMatrix.swap(bdm);
  swhGetMatrixAnd(DominateMatrix, PostDominateMatrix, Matrix0);
}

void
SwhNeededMfInfo::swhGetMatrixAnd(std::vector<std::vector<int>> Matrix1,
                                   std::vector<std::vector<int>> Matrix2, std::vector<std::vector<int>> &Matrix0){
  int MTSize = Matrix1.size();
  Matrix0 = std::vector<std::vector<int>>(MTSize,std::vector<int>(MTSize,0));
  for (unsigned I = 0; I < Matrix1.size(); I++) {
    for (unsigned J = 0; J < Matrix1.size(); ++J) {
      if (Matrix1[I][J]==1 && Matrix2[J][I]==1)
        Matrix0[I][J]=1;
    }
  }
}

void SwhSeseRegion::initLRU(const TargetRegisterInfo &TRI){
  assert(ParentFunc->getRegInfo().tracksLiveness() &&
         "Candidate's Machine Function must track liveness");
  // Only initialize once.
  if (LRUWasSet)
  return;
  LRUWasSet = true;
  LRU.init(TRI);
  UsedInSequence.init(TRI);
  for (auto I :BlockList) {
    MachineBasicBlock *MBB = ParentFunc->getBlockNumbered(I);
    LRU.addLiveOuts(*MBB);
    // Compute liveness from the end of the block up to the beginning of the
    // outlining candidate.
    std::for_each(MBB->rbegin(), MBB->rend(),
    [this](MachineInstr &MI) { LRU.stepBackward(MI); });
    std::for_each(MBB->rbegin(), MBB->rend(),
    [this](MachineInstr &MI) { UsedInSequence.accumulate(MI); });
  }
}
bool SwhSeseRegion::isContainsStackOperation() {
  return true;
}
bool SwhSeseRegion::isEndWithMoreThanOneTerminator() const {
  MachineBasicBlock *EndMbb = ParentFunc->getBlockNumbered(BlockList[1]);
  return (std::next(EndMbb->getFirstTerminator())!=EndMbb->end() && EndMbb->getFirstTerminator()!=EndMbb->end());
}
bool SwhSeseRegion::checkCompleteness() {
  //宽度优先搜索顺序，同级节点，按照successor顺序来排序

  std::vector<int> BlockListCompleting;
  MachineBasicBlock *Start = ParentFunc->getBlockNumbered(BlockList[0]);
  MachineBasicBlock *End = ParentFunc->getBlockNumbered(BlockList[1]);
  BlockListCompleting.push_back(Start->getNumber());
  BlockListCompleting.push_back(End->getNumber());
  for (unsigned long I = 0; I < BlockListCompleting.size(); ++I) {
    if (I==1)continue;
    for (MachineBasicBlock *Succ:ParentFunc->getBlockNumbered(BlockListCompleting[I])->successors()) {
      if (!listContains(BlockList, Succ->getNumber())){
        return false;
      }
      if (!listContains(BlockListCompleting, Succ->getNumber()))
        BlockListCompleting.push_back(Succ->getNumber());
    }
  }

  return true;
}

bool SwhSeseRegion::checkPostCompleteness() {
  //宽度优先搜索顺序，同级节点，按照predecessor顺序来排序
  std::vector<int> BlockListCompleting;
  MachineBasicBlock *Start = ParentFunc->getBlockNumbered(BlockList[0]);
  MachineBasicBlock *End = ParentFunc->getBlockNumbered(BlockList[1]);
  BlockListCompleting.push_back(Start->getNumber());
  BlockListCompleting.push_back(End->getNumber());
  for (unsigned long I = 1; I < BlockListCompleting.size(); ++I) {
    for (MachineBasicBlock *Pred:ParentFunc->getBlockNumbered(BlockListCompleting[I])->predecessors()) {
      if (!listContains(BlockList, Pred->getNumber())){
        return false;
      }
      if (!listContains(BlockListCompleting, Pred->getNumber()))
        BlockListCompleting.push_back(Pred->getNumber());
    }
  }

  return true;
}

void outliner::AbstractedFunction::emitMark() {
  errs()<<"\nAbstracted from "<<RegionCandidates.size()<<" location.\n";
  for (SwhSeseRegion Region:RegionCandidates) {
    errs()<<Region.ParentFunc->getName()<<" :";
    for (unsigned long I = 0; I < Region.BlockList.size(); ++I) {
      errs()<<" "<<Region.BlockList[I];
    }
    errs()<<"\n";
  }
  errs()<<"Size of the the duplicate code on each location is "<<RegionSize<<" bytes.\n";
  errs()<<"The frame overhead and the call overhead is "<<FrameOverhead<<", "<<RegionCandidates.begin()->getCallOverhead()<<". \n";
  errs()<<"The final benefit is "<<AbstractedBenefit<<" bytes. ";
  
  
}
} //end namespace outliner
} //end namespace llvm


namespace {

/// Maps \p MachineInstrs to unsigned integers and stores the mappings.
struct InstructionMapperSWH {

  /// The next available integer to assign to a \p MachineInstr that
  /// cannot be outlined.
  ///
  /// Set to -3 for compatability with \p DenseMapInfo<unsigned>.
  unsigned IllegalInstrNumber = -3;

  /// The next available integer to assign to a \p MachineInstr that can
  /// be outlined.
  unsigned LegalInstrNumber = 0;

  /// Correspondence from \p MachineInstrs to unsigned integers.
  DenseMap<MachineInstr *, unsigned, MachineInstrExpressionTrait>
      InstructionIntegerMap;

  /// Correspondence between \p MachineBasicBlocks and target-defined flags.
  DenseMap<MachineBasicBlock *, unsigned> MBBFlagsMap;

  /// The vector of unsigned integers that the module is mapped to.
  std::vector<unsigned> UnsignedVec;

  /// Stores the location of the instruction associated with the integer
  /// at index i in \p UnsignedVec for each index i.
  std::vector<MachineBasicBlock::iterator> InstrList;

  // Set if we added an illegal number in the previous step.
  // Since each illegal number is unique, we only need one of them between
  // each range of legal numbers. This lets us make sure we don't add more
  // than one illegal number per range.
  bool AddedIllegalLastTime = false;

  /// Maps \p *It to a legal integer.
  ///
  /// Updates \p CanOutlineWithPrevInstr, \p HaveLegalRange, \p InstrListForMBB,
  /// \p UnsignedVecForMBB, \p InstructionIntegerMap, and \p LegalInstrNumber.
  ///
  /// \returns The integer that \p *It was mapped to.
  unsigned mapToLegalUnsigned(
      MachineBasicBlock::iterator &It, bool &CanOutlineWithPrevInstr,
      bool &HaveLegalRange, unsigned &NumLegalInBlock,
      std::vector<unsigned> &UnsignedVecForMBB,
      std::vector<MachineBasicBlock::iterator> &InstrListForMBB) {
    // We added something legal, so we should unset the AddedLegalLastTime
    // flag.
    AddedIllegalLastTime = false;

    // If we have at least two adjacent legal instructions (which may have
    // invisible instructions in between), remember that.
    if (CanOutlineWithPrevInstr)
      HaveLegalRange = true;
    CanOutlineWithPrevInstr = true;

    // Keep track of the number of legal instructions we insert.
    NumLegalInBlock++;

    // Get the integer for this instruction or give it the current
    // LegalInstrNumber.
    InstrListForMBB.push_back(It);
    MachineInstr &MI = *It;
    bool WasInserted;
    DenseMap<MachineInstr *, unsigned, MachineInstrExpressionTrait>::iterator
        ResultIt;
    std::tie(ResultIt, WasInserted) =
        InstructionIntegerMap.insert(std::make_pair(&MI, LegalInstrNumber));
    unsigned MINumber = ResultIt->second;

    // There was an insertion.
    if (WasInserted)
      LegalInstrNumber++;

    UnsignedVecForMBB.push_back(MINumber);

    // Make sure we don't overflow or use any integers reserved by the DenseMap.
    if (LegalInstrNumber >= IllegalInstrNumber)
      report_fatal_error("Instruction mapping overflow!");

    assert(LegalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
           "Tried to assign DenseMap tombstone or empty key to instruction.");
    assert(LegalInstrNumber != DenseMapInfo<unsigned>::getTombstoneKey() &&
           "Tried to assign DenseMap tombstone or empty key to instruction.");

    return MINumber;
  }

  /// Maps \p *It to an illegal integer.
  ///
  /// Updates \p InstrListForMBB, \p UnsignedVecForMBB, and \p
  /// IllegalInstrNumber.
  ///
  /// \returns The integer that \p *It was mapped to.
  unsigned mapToIllegalUnsigned(
      MachineBasicBlock::iterator &It, bool &CanOutlineWithPrevInstr,
      std::vector<unsigned> &UnsignedVecForMBB,
      std::vector<MachineBasicBlock::iterator> &InstrListForMBB) {
    // Can't outline an illegal instruction. Set the flag.
    CanOutlineWithPrevInstr = false;

    // Only add one illegal number per range of legal numbers.
    if (AddedIllegalLastTime)
      return IllegalInstrNumber;

    // Remember that we added an illegal number last time.
    AddedIllegalLastTime = true;
    unsigned MINumber = IllegalInstrNumber;

    InstrListForMBB.push_back(It);
    UnsignedVecForMBB.push_back(IllegalInstrNumber);
    IllegalInstrNumber--;

    assert(LegalInstrNumber < IllegalInstrNumber &&
           "Instruction mapping overflow!");

    assert(IllegalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
           "IllegalInstrNumber cannot be DenseMap tombstone or empty key!");

    assert(IllegalInstrNumber != DenseMapInfo<unsigned>::getTombstoneKey() &&
           "IllegalInstrNumber cannot be DenseMap tombstone or empty key!");

    return MINumber;
  }

  /// Transforms a \p MachineBasicBlock into a \p vector of \p unsigneds
  /// and appends it to \p UnsignedVec and \p InstrList.
  ///
  /// Two instructions are assigned the same integer if they are identical.
  /// If an instruction is deemed unsafe to outline, then it will be assigned an
  /// unique integer. The resulting mapping is placed into a suffix tree and
  /// queried for candidates.
  ///
  /// \param MBB The \p MachineBasicBlock to be translated into integers.
  /// \param TII \p TargetInstrInfo for the function.
  void convertToUnsignedVec(MachineBasicBlock &MBB,
                            const TargetInstrInfo &TII) {
    unsigned Flags = 0;

    // Don't even map in this case.
    if (!TII.isMBBSafeToOutlineFrom(MBB, Flags))
      return;

    // Store info for the MBB for later outlining.
    MBBFlagsMap[&MBB] = Flags;

    MachineBasicBlock::iterator It = MBB.begin();

    // The number of instructions in this block that will be considered for
    // outlining.
    unsigned NumLegalInBlock = 0;

    // True if we have at least two legal instructions which aren't separated
    // by an illegal instruction.
    bool HaveLegalRange = false;

    // True if we can perform outlining given the last mapped (non-invisible)
    // instruction. This lets us know if we have a legal range.
    bool CanOutlineWithPrevInstr = false;

    // FIXME: Should this all just be handled in the target, rather than using
    // repeated calls to getOutliningType?
    std::vector<unsigned> UnsignedVecForMBB;
    std::vector<MachineBasicBlock::iterator> InstrListForMBB;

    for (MachineBasicBlock::iterator Et = MBB.end(); It != Et; ++It) {
      // Keep track of where this instruction is in the module.
      switch (TII.getOutliningType(It, Flags)) {
      case InstrType::Illegal:
        mapToIllegalUnsigned(It, CanOutlineWithPrevInstr, UnsignedVecForMBB,
                             InstrListForMBB);
        break;

      case InstrType::Legal:
        mapToLegalUnsigned(It, CanOutlineWithPrevInstr, HaveLegalRange,
                           NumLegalInBlock, UnsignedVecForMBB, InstrListForMBB);
        break;

      case InstrType::LegalTerminator:
        mapToLegalUnsigned(It, CanOutlineWithPrevInstr, HaveLegalRange,
                           NumLegalInBlock, UnsignedVecForMBB, InstrListForMBB);
        // The instruction also acts as a terminator, so we have to record that
        // in the string.
        mapToIllegalUnsigned(It, CanOutlineWithPrevInstr, UnsignedVecForMBB,
                             InstrListForMBB);
        break;

      case InstrType::Invisible:
        // Normally this is set by mapTo(Blah)Unsigned, but we just want to
        // skip this instruction. So, unset the flag here.
        AddedIllegalLastTime = false;
        break;
      }
    }

    // Are there enough legal instructions in the block for outlining to be
    // possible?
    if (HaveLegalRange) {
      // After we're done every insertion, uniquely terminate this part of the
      // "string". This makes sure we won't match across basic block or function
      // boundaries since the "end" is encoded uniquely and thus appears in no
      // repeated substring.
      mapToIllegalUnsigned(It, CanOutlineWithPrevInstr, UnsignedVecForMBB,
                           InstrListForMBB);
      llvm::append_range(InstrList, InstrListForMBB);
      llvm::append_range(UnsignedVec, UnsignedVecForMBB);
    }
  }

  InstructionMapperSWH() {
    // Make sure that the implementation of DenseMapInfo<unsigned> hasn't
    // changed.
    assert(DenseMapInfo<unsigned>::getEmptyKey() == (unsigned)-1 &&
           "DenseMapInfo<unsigned>'s empty key isn't -1!");
    assert(DenseMapInfo<unsigned>::getTombstoneKey() == (unsigned)-2 &&
           "DenseMapInfo<unsigned>'s tombstone key isn't -2!");
  }
};

/// An interprocedural pass which finds repeated sequences of
/// instructions and replaces them with calls to functions.
///
/// Each instruction is mapped to an unsigned integer and placed in a string.
/// The resulting mapping is then placed in a \p SuffixTree. The \p SuffixTree
/// is then repeatedly queried for repeated sequences of instructions. Each
/// non-overlapping repeated sequence is then placed in its own
/// \p MachineFunction and each instance is then replaced with a call to that
/// function.
struct MachineOutlinerSWH : public ModulePass {

  static char ID;

  /// Set to true if the outliner should consider functions with
  /// linkonceodr linkage.
  bool OutlineFromLinkOnceODRs = false;

  /// The current repeat number of machine outlining.
  unsigned OutlineRepeatedNum = 0;

  /// Set to true if the outliner should run on all functions in the module
  /// considered safe for outlining.
  /// Set to true by default for compatibility with llc's -run-pass option.
  /// Set when the pass is constructed in TargetPassConfig.
  bool RunOnAllFunctions = true;

  StringRef getPassName() const override { return "Machine Outliner SWH"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<MachineModuleInfoWrapperPass>();
    AU.addPreserved<MachineModuleInfoWrapperPass>();
    AU.setPreservesAll();
    ModulePass::getAnalysisUsage(AU);
  }

  MachineOutlinerSWH() : ModulePass(ID) {
    initializeMachineOutlinerPass(*PassRegistry::getPassRegistry());
  }

  /// Remark output explaining that not outlining a set of candidates would be
  /// better than outlining that set.
  void emitNotOutliningCheaperRemark(
      unsigned StringLen, std::vector<Candidate> &CandidatesForRepeatedSeq,
      OutlinedFunction &OF);

  /// Remark output explaining that a function was outlined.
  void emitOutlinedFunctionRemark(OutlinedFunction &OF);

  /// Find all repeated substrings that satisfy the outlining cost model by
  /// constructing a suffix tree.
  ///
  /// If a substring appears at least twice, then it must be represented by
  /// an internal node which appears in at least two suffixes. Each suffix
  /// is represented by a leaf node. To do this, we visit each internal node
  /// in the tree, using the leaf children of each internal node. If an
  /// internal node represents a beneficial substring, then we use each of
  /// its leaf children to find the locations of its substring.
  ///
  /// \param Mapper Contains outlining mapping information.
  /// \param[out] FunctionList Filled with a list of \p OutlinedFunctions
  /// each type of candidate.
  void findCandidates(InstructionMapperSWH &Mapper,
                      std::vector<OutlinedFunction> &FunctionList);

  /// Replace the sequences of instructions represented by \p OutlinedFunctions
  /// with calls to functions.
  ///
  /// \param M The module we are outlining from.
  /// \param FunctionList A list of functions to be inserted into the module.
  /// \param Mapper Contains the instruction mappings for the module.
  bool outline(Module &M, std::vector<OutlinedFunction> &FunctionList,
               InstructionMapperSWH &Mapper, unsigned &OutlinedFunctionNum);

  /// Creates a function for \p OF and inserts it into the module.
  MachineFunction *createOutlinedFunction(Module &M, OutlinedFunction &OF,
                                          InstructionMapperSWH &Mapper,
                                          unsigned Name);

  /// Calls 'doOutline()' 1 + OutlinerReruns times.
  bool runOnModule(Module &M) override;

  /// Construct a suffix tree on the instructions in \p M and outline repeated
  /// strings from that tree.
  bool doOutline(Module &M, unsigned &OutlinedFunctionNum);

  /// Return a DISubprogram for OF if one exists, and null otherwise. Helper
  /// function for remark emission.
  DISubprogram *getSubprogramOrNull(const OutlinedFunction &OF) {
    for (const Candidate &C : OF.Candidates)
      if (MachineFunction *MF = C.getMF())
        if (DISubprogram *SP = MF->getFunction().getSubprogram())
          return SP;
    return nullptr;
  }

  /// Populate and \p InstructionMapper with instruction-to-integer mappings.
  /// These are used to construct a suffix tree.
  void populateMapper(InstructionMapperSWH &Mapper, Module &M,
                      MachineModuleInfo &MMI);

  /// Initialize information necessary to output a size remark.
  /// FIXME: This should be handled by the pass manager, not the outliner.
  /// FIXME: This is nearly identical to the initSizeRemarkInfo in the legacy
  /// pass manager.
  void initSizeRemarkInfo(const Module &M, const MachineModuleInfo &MMI,
                          StringMap<unsigned> &FunctionToInstrCount);

  /// Emit the remark.
  // FIXME: This should be handled by the pass manager, not the outliner.
  void
  emitInstrCountChangedRemark(const Module &M, const MachineModuleInfo &MMI,
                              const StringMap<unsigned> &FunctionToInstrCount);

//Functions Create by SWH
  /// do interprocedural outline on module M
  /// \param M Module
  void swhDoInterproceduralOutline(Module &M);

  void swhViewAllCFGModule(Module &M);
};

} // Anonymous namespace.

char MachineOutlinerSWH::ID = 0;

namespace llvm {
ModulePass *createMachineOutlinerSWHPass(bool RunOnAllFunctions) {
  MachineOutlinerSWH *OL = new MachineOutlinerSWH();
  OL->RunOnAllFunctions = RunOnAllFunctions;
  return OL;
}

} // namespace llvm

INITIALIZE_PASS(MachineOutlinerSWH, DEBUG_TYPE, "Machine Function Outliner SWH", false,
                false)

void checkSucc(AbstractedFunction AF);

void MachineOutlinerSWH::emitNotOutliningCheaperRemark(
    unsigned StringLen, std::vector<Candidate> &CandidatesForRepeatedSeq,
    OutlinedFunction &OF) {
  // FIXME: Right now, we arbitrarily choose some Candidate from the
  // OutlinedFunction. This isn't necessarily fixed, nor does it have to be.
  // We should probably sort these by function name or something to make sure
  // the remarks are stable.
  Candidate &C = CandidatesForRepeatedSeq.front();
  MachineOptimizationRemarkEmitter MORE(*(C.getMF()), nullptr);
  MORE.emit([&]() {
    MachineOptimizationRemarkMissed R(DEBUG_TYPE, "NotOutliningCheaper",
                                      C.front()->getDebugLoc(), C.getMBB());
    R << "Did not outline " << NV("Length", StringLen) << " instructions"
      << " from " << NV("NumOccurrences", CandidatesForRepeatedSeq.size())
      << " locations."
      << " Bytes from outlining all occurrences ("
      << NV("OutliningCost", OF.getOutliningCost()) << ")"
      << " >= Unoutlined instruction bytes ("
      << NV("NotOutliningCost", OF.getNotOutlinedCost()) << ")"
      << " (Also found at: ";

    // Tell the user the other places the candidate was found.
    for (unsigned I = 1, E = CandidatesForRepeatedSeq.size(); I < E; I++) {
      R << NV((Twine("OtherStartLoc") + Twine(I)).str(),
              CandidatesForRepeatedSeq[I].front()->getDebugLoc());
      if (I != E - 1)
        R << ", ";
    }

    R << ")";
    return R;
  });
}

void MachineOutlinerSWH::emitOutlinedFunctionRemark(OutlinedFunction &OF) {
  MachineBasicBlock *MBB = &*OF.MF->begin();
  MachineOptimizationRemarkEmitter MORE(*OF.MF, nullptr);
  MachineOptimizationRemark R(DEBUG_TYPE, "OutlinedFunction",
                              MBB->findDebugLoc(MBB->begin()), MBB);
  R << "Saved " << NV("OutliningBenefit", OF.getBenefit()) << " bytes by "
    << "outlining " << NV("Length", OF.getNumInstrs()) << " instructions "
    << "from " << NV("NumOccurrences", OF.getOccurrenceCount())
    << " locations. "
    << "(Found at: ";

  // Tell the user the other places the candidate was found.
  for (size_t I = 0, E = OF.Candidates.size(); I < E; I++) {

    R << NV((Twine("StartLoc") + Twine(I)).str(),
            OF.Candidates[I].front()->getDebugLoc());
    if (I != E - 1)
      R << ", ";
  }

  R << ")";

  MORE.emit(R);
}

void MachineOutlinerSWH::findCandidates(
    InstructionMapperSWH &Mapper, std::vector<OutlinedFunction> &FunctionList) {
  FunctionList.clear();
  SuffixTree ST(Mapper.UnsignedVec);

  // First, find all of the repeated substrings in the tree of minimum length
  // 2.
  std::vector<Candidate> CandidatesForRepeatedSeq;
  for (auto It = ST.begin(), Et = ST.end(); It != Et; ++It) {
    CandidatesForRepeatedSeq.clear();
    SuffixTree::RepeatedSubstring RS = *It;
    unsigned StringLen = RS.Length;
    for (const unsigned &StartIdx : RS.StartIndices) {
      unsigned EndIdx = StartIdx + StringLen - 1;
      // Trick: Discard some candidates that would be incompatible with the
      // ones we've already found for this sequence. This will save us some
      // work in candidate selection.
      //
      // If two candidates overlap, then we can't outline them both. This
      // happens when we have candidates that look like, say
      //
      // AA (where each "A" is an instruction).
      //
      // We might have some portion of the module that looks like this:
      // AAAAAA (6 A's)
      //
      // In this case, there are 5 different copies of "AA" in this range, but
      // at most 3 can be outlined. If only outlining 3 of these is going to
      // be unbeneficial, then we ought to not bother.
      //
      // Note that two things DON'T overlap when they look like this:
      // start1...end1 .... start2...end2
      // That is, one must either
      // * End before the other starts
      // * Start after the other ends
      if (llvm::all_of(CandidatesForRepeatedSeq, [&StartIdx,
                                                  &EndIdx](const Candidate &C) {
            return (EndIdx < C.getStartIdx() || StartIdx > C.getEndIdx());
          })) {
        // It doesn't overlap with anything, so we can outline it.
        // Each sequence is over [StartIt, EndIt].
        // Save the candidate and its location.

        MachineBasicBlock::iterator StartIt = Mapper.InstrList[StartIdx];
        MachineBasicBlock::iterator EndIt = Mapper.InstrList[EndIdx];
        MachineBasicBlock *MBB = StartIt->getParent();

        CandidatesForRepeatedSeq.emplace_back(StartIdx, StringLen, StartIt,
                                              EndIt, MBB, FunctionList.size(),
                                              Mapper.MBBFlagsMap[MBB]);
      }
    }

    // We've found something we might want to outline.
    // Create an OutlinedFunction to store it and check if it'd be beneficial
    // to outline.
    if (CandidatesForRepeatedSeq.size() < 2)
      continue;

    // Arbitrarily choose a TII from the first candidate.
    // FIXME: Should getOutliningCandidateInfo move to TargetMachine?
    const TargetInstrInfo *TII =
        CandidatesForRepeatedSeq[0].getMF()->getSubtarget().getInstrInfo();

    OutlinedFunction OF =
        TII->getOutliningCandidateInfo(CandidatesForRepeatedSeq);

    // If we deleted too many candidates, then there's nothing worth outlining.
    // FIXME: This should take target-specified instruction sizes into account.
    if (OF.Candidates.size() < 2)
      continue;

    // Is it better to outline this candidate than not?
    if (OF.getBenefit() < 1) {
      emitNotOutliningCheaperRemark(StringLen, CandidatesForRepeatedSeq, OF);
      continue;
    }

    FunctionList.push_back(OF);
  }
}

MachineFunction *MachineOutlinerSWH::createOutlinedFunction(
    Module &M, OutlinedFunction &OF, InstructionMapperSWH &Mapper, unsigned Name) {

  // Create the function name. This should be unique.
  // FIXME: We should have a better naming scheme. This should be stable,
  // regardless of changes to the outliner's cost model/traversal order.
  std::string FunctionName = "OUTLINED_FUNCTION_";
  if (OutlineRepeatedNum > 0)
    FunctionName += std::to_string(OutlineRepeatedNum + 1) + "_";
  FunctionName += std::to_string(Name);

  // Create the function using an IR-level function.
  LLVMContext &C = M.getContext();
  Function *F = Function::Create(FunctionType::get(Type::getVoidTy(C), false),
                                 Function::ExternalLinkage, FunctionName, M);

  // NOTE: If this is linkonceodr, then we can take advantage of linker deduping
  // which gives us better results when we outline from linkonceodr functions.
  F->setLinkage(GlobalValue::InternalLinkage);
  F->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);

  // Set optsize/minsize, so we don't insert padding between outlined
  // functions.
  F->addFnAttr(Attribute::OptimizeForSize);
  F->addFnAttr(Attribute::MinSize);

  // Include target features from an arbitrary candidate for the outlined
  // function. This makes sure the outlined function knows what kinds of
  // instructions are going into it. This is fine, since all parent functions
  // must necessarily support the instructions that are in the outlined region.
  Candidate &FirstCand = OF.Candidates.front();
  const Function &ParentFn = FirstCand.getMF()->getFunction();
  if (ParentFn.hasFnAttribute("target-features"))
    F->addFnAttr(ParentFn.getFnAttribute("target-features"));

  // Set nounwind, so we don't generate eh_frame.
  if (llvm::all_of(OF.Candidates, [](const outliner::Candidate &C) {
        return C.getMF()->getFunction().hasFnAttribute(Attribute::NoUnwind);
      }))
    F->addFnAttr(Attribute::NoUnwind);

  BasicBlock *EntryBB = BasicBlock::Create(C, "entry", F);
  IRBuilder<> Builder(EntryBB);
  Builder.CreateRetVoid();

  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfoWrapperPass>().getMMI();
  MachineFunction &MF = MMI.getOrCreateMachineFunction(*F);
  MachineBasicBlock &MBB = *MF.CreateMachineBasicBlock();
  const TargetSubtargetInfo &STI = MF.getSubtarget();
  const TargetInstrInfo &TII = *STI.getInstrInfo();

  // Insert the new function into the module.
  MF.insert(MF.begin(), &MBB);

  MachineFunction *OriginalMF = FirstCand.front()->getMF();
  const std::vector<MCCFIInstruction> &Instrs =
      OriginalMF->getFrameInstructions();
  for (auto I = FirstCand.front(), E = std::next(FirstCand.back()); I != E;
       ++I) {
    if (I->isDebugInstr())
      continue;
    MachineInstr *NewMI = MF.CloneMachineInstr(&*I);
    if (I->isCFIInstruction()) {
      unsigned CFIIndex = NewMI->getOperand(0).getCFIIndex();
      MCCFIInstruction CFI = Instrs[CFIIndex];
      (void)MF.addFrameInst(CFI);
    }
    NewMI->dropMemRefs(MF);

    // Don't keep debug information for outlined instructions.
    NewMI->setDebugLoc(DebugLoc());
    MBB.insert(MBB.end(), NewMI);
  }

  // Set normal properties for a late MachineFunction.
  MF.getProperties().reset(MachineFunctionProperties::Property::IsSSA);
  MF.getProperties().set(MachineFunctionProperties::Property::NoPHIs);
  MF.getProperties().set(MachineFunctionProperties::Property::NoVRegs);
  MF.getProperties().set(MachineFunctionProperties::Property::TracksLiveness);
  MF.getRegInfo().freezeReservedRegs(MF);

  // Compute live-in set for outlined fn
  const MachineRegisterInfo &MRI = MF.getRegInfo();
  const TargetRegisterInfo &TRI = *MRI.getTargetRegisterInfo();
  LivePhysRegs LiveIns(TRI);
  for (auto &Cand : OF.Candidates) {
    // Figure out live-ins at the first instruction.
    MachineBasicBlock &OutlineBB = *Cand.front()->getParent();
    LivePhysRegs CandLiveIns(TRI);
    CandLiveIns.addLiveOuts(OutlineBB);
    for (const MachineInstr &MI :
         reverse(make_range(Cand.front(), OutlineBB.end())))
      CandLiveIns.stepBackward(MI);

    // The live-in set for the outlined function is the union of the live-ins
    // from all the outlining points.
    for (MCPhysReg Reg : CandLiveIns)
      LiveIns.addReg(Reg);
  }
  addLiveIns(MBB, LiveIns);

  TII.buildOutlinedFrame(MBB, MF, OF);

  // If there's a DISubprogram associated with this outlined function, then
  // emit debug info for the outlined function.
  if (DISubprogram *SP = getSubprogramOrNull(OF)) {
    // We have a DISubprogram. Get its DICompileUnit.
    DICompileUnit *CU = SP->getUnit();
    DIBuilder DB(M, true, CU);
    DIFile *Unit = SP->getFile();
    Mangler Mg;
    // Get the mangled name of the function for the linkage name.
    std::string Dummy;
    llvm::raw_string_ostream MangledNameStream(Dummy);
    Mg.getNameWithPrefix(MangledNameStream, F, false);

    DISubprogram *OutlinedSP = DB.createFunction(
        Unit /* Context */, F->getName(), StringRef(MangledNameStream.str()),
        Unit /* File */,
        0 /* Line 0 is reserved for compiler-generated code. */,
        DB.createSubroutineType(DB.getOrCreateTypeArray(None)), /* void type */
        0, /* Line 0 is reserved for compiler-generated code. */
        DINode::DIFlags::FlagArtificial /* Compiler-generated code. */,
        /* Outlined code is optimized code by definition. */
        DISubprogram::SPFlagDefinition | DISubprogram::SPFlagOptimized);

    // Don't add any new variables to the subprogram.
    DB.finalizeSubprogram(OutlinedSP);

    // Attach subprogram to the function.
    F->setSubprogram(OutlinedSP);
    // We're done with the DIBuilder.
    DB.finalize();
  }

  return &MF;
}

bool MachineOutlinerSWH::outline(Module &M,
                              std::vector<OutlinedFunction> &FunctionList,
                              InstructionMapperSWH &Mapper,
                              unsigned &OutlinedFunctionNum) {

  bool OutlinedSomething = false;

  // Sort by benefit. The most beneficial functions should be outlined first.
  llvm::stable_sort(FunctionList, [](const OutlinedFunction &LHS,
                                     const OutlinedFunction &RHS) {
    return LHS.getBenefit() > RHS.getBenefit();
  });

  // Walk over each function, outlining them as we go along. Functions are
  // outlined greedily, based off the sort above.
  for (OutlinedFunction &OF : FunctionList) {
    // If we outlined something that overlapped with a candidate in a previous
    // step, then we can't outline from it.
    erase_if(OF.Candidates, [&Mapper](Candidate &C) {
      return std::any_of(
          Mapper.UnsignedVec.begin() + C.getStartIdx(),
          Mapper.UnsignedVec.begin() + C.getEndIdx() + 1,
          [](unsigned I) { return (I == static_cast<unsigned>(-1)); });
    });

    // If we made it unbeneficial to outline this function, skip it.
    if (OF.getBenefit() < 1)
      continue;

    // It's beneficial. Create the function and outline its sequence's
    // occurrences.
    OF.MF = createOutlinedFunction(M, OF, Mapper, OutlinedFunctionNum);
    emitOutlinedFunctionRemark(OF);
    FunctionsCreated_swh++;
    OutlinedFunctionNum++; // Created a function, move to the next name.
    MachineFunction *MF = OF.MF;
    const TargetSubtargetInfo &STI = MF->getSubtarget();
    const TargetInstrInfo &TII = *STI.getInstrInfo();

    // Replace occurrences of the sequence with calls to the new function.
    for (Candidate &C : OF.Candidates) {
      MachineBasicBlock &MBB = *C.getMBB();
      MachineBasicBlock::iterator StartIt = C.front();
      MachineBasicBlock::iterator EndIt = C.back();

      // Insert the call.
      auto CallInst = TII.insertOutlinedCall(M, MBB, StartIt, *MF, C);

      // If the caller tracks liveness, then we need to make sure that
      // anything we outline doesn't break liveness assumptions. The outlined
      // functions themselves currently don't track liveness, but we should
      // make sure that the ranges we yank things out of aren't wrong.
      if (MBB.getParent()->getProperties().hasProperty(
              MachineFunctionProperties::Property::TracksLiveness)) {
        // The following code is to add implicit def operands to the call
        // instruction. It also updates call site information for moved
        // code.
        SmallSet<Register, 2> UseRegs, DefRegs;
        // Copy over the defs in the outlined range.
        // First inst in outlined range <-- Anything that's defined in this
        // ...                           .. range has to be added as an
        // implicit Last inst in outlined range  <-- def to the call
        // instruction. Also remove call site information for outlined block
        // of code. The exposed uses need to be copied in the outlined range.
        for (MachineBasicBlock::reverse_iterator
                 Iter = EndIt.getReverse(),
                 Last = std::next(CallInst.getReverse());
             Iter != Last; Iter++) {
          MachineInstr *MI = &*Iter;
          for (MachineOperand &MOP : MI->operands()) {
            // Skip over anything that isn't a register.
            if (!MOP.isReg())
              continue;

            if (MOP.isDef()) {
              // Introduce DefRegs set to skip the redundant register.
              DefRegs.insert(MOP.getReg());
              if (UseRegs.count(MOP.getReg()))
                // Since the regiester is modeled as defined,
                // it is not necessary to be put in use register set.
                UseRegs.erase(MOP.getReg());
            } else if (!MOP.isUndef()) {
              // Any register which is not undefined should
              // be put in the use register set.
              UseRegs.insert(MOP.getReg());
            }
          }
          if (MI->isCandidateForCallSiteEntry())
            MI->getMF()->eraseCallSiteInfo(MI);
        }

        for (const Register &I : DefRegs)
          // If it's a def, add it to the call instruction.
          CallInst->addOperand(
              MachineOperand::CreateReg(I, true, /* isDef = true */
                                        true /* isImp = true */));

        for (const Register &I : UseRegs)
          // If it's a exposed use, add it to the call instruction.
          CallInst->addOperand(
              MachineOperand::CreateReg(I, false, /* isDef = false */
                                        true /* isImp = true */));
      }

      // Erase from the point after where the call was inserted up to, and
      // including, the final instruction in the sequence.
      // Erase needs one past the end, so we need std::next there too.
      MBB.erase(std::next(StartIt), std::next(EndIt));

      // Keep track of what we removed by marking them all as -1.
      std::for_each(Mapper.UnsignedVec.begin() + C.getStartIdx(),
                    Mapper.UnsignedVec.begin() + C.getEndIdx() + 1,
                    [](unsigned &I) { I = static_cast<unsigned>(-1); });
      OutlinedSomething = true;

      // Statistics.
      NumOutlined_swh++;
    }
  }

  LLVM_DEBUG(dbgs() << "OutlinedSomething = " << OutlinedSomething << "\n";);
  return OutlinedSomething;
}

void MachineOutlinerSWH::populateMapper(InstructionMapperSWH &Mapper, Module &M,
                                     MachineModuleInfo &MMI) {
  // Build instruction mappings for each function in the module. Start by
  // iterating over each Function in M.
  for (Function &F : M) {

    // If there's nothing in F, then there's no reason to try and outline from
    // it.
    if (F.empty())
      continue;

    // There's something in F. Check if it has a MachineFunction associated with
    // it.
    MachineFunction *MF = MMI.getMachineFunction(F);

    // If it doesn't, then there's nothing to outline from. Move to the next
    // Function.
    if (!MF)
      continue;

    const TargetInstrInfo *TII = MF->getSubtarget().getInstrInfo();

    if (!RunOnAllFunctions && !TII->shouldOutlineFromFunctionByDefault(*MF))
      continue;

    // We have a MachineFunction. Ask the target if it's suitable for outlining.
    // If it isn't, then move on to the next Function in the module.
    if (!TII->isFunctionSafeToOutlineFrom(*MF, OutlineFromLinkOnceODRs))
      continue;

    // We have a function suitable for outlining. Iterate over every
    // MachineBasicBlock in MF and try to map its instructions to a list of
    // unsigned integers.
    for (MachineBasicBlock &MBB : *MF) {
      // If there isn't anything in MBB, then there's no point in outlining from
      // it.
      // If there are fewer than 2 instructions in the MBB, then it can't ever
      // contain something worth outlining.
      // FIXME: This should be based off of the maximum size in B of an outlined
      // call versus the size in B of the MBB.
      if (MBB.empty() || MBB.size() < 2)
        continue;

      // Check if MBB could be the target of an indirect branch. If it is, then
      // we don't want to outline from it.
      if (MBB.hasAddressTaken())
        continue;

      // MBB is suitable for outlining. Map it to a list of unsigneds.
      Mapper.convertToUnsignedVec(MBB, *TII);
    }
  }
}

void MachineOutlinerSWH::initSizeRemarkInfo(
    const Module &M, const MachineModuleInfo &MMI,
    StringMap<unsigned> &FunctionToInstrCount) {
  // Collect instruction counts for every function. We'll use this to emit
  // per-function size remarks later.
  for (const Function &F : M) {
    MachineFunction *MF = MMI.getMachineFunction(F);

    // We only care about MI counts here. If there's no MachineFunction at this
    // point, then there won't be after the outliner runs, so let's move on.
    if (!MF)
      continue;
    FunctionToInstrCount[F.getName().str()] = MF->getInstructionCount();
  }
}

void MachineOutlinerSWH::emitInstrCountChangedRemark(
    const Module &M, const MachineModuleInfo &MMI,
    const StringMap<unsigned> &FunctionToInstrCount) {
  // Iterate over each function in the module and emit remarks.
  // Note that we won't miss anything by doing this, because the outliner never
  // deletes functions.
  for (const Function &F : M) {
    MachineFunction *MF = MMI.getMachineFunction(F);

    // The outliner never deletes functions. If we don't have a MF here, then we
    // didn't have one prior to outlining either.
    if (!MF)
      continue;

    std::string Fname = std::string(F.getName());
    unsigned FnCountAfter = MF->getInstructionCount();
    unsigned FnCountBefore = 0;

    // Check if the function was recorded before.
    auto It = FunctionToInstrCount.find(Fname);

    // Did we have a previously-recorded size? If yes, then set FnCountBefore
    // to that.
    if (It != FunctionToInstrCount.end())
      FnCountBefore = It->second;

    // Compute the delta and emit a remark if there was a change.
    int64_t FnDelta = static_cast<int64_t>(FnCountAfter) -
                      static_cast<int64_t>(FnCountBefore);
    if (FnDelta == 0)
      continue;

    MachineOptimizationRemarkEmitter MORE(*MF, nullptr);
    MORE.emit([&]() {
      MachineOptimizationRemarkAnalysis R("size-info", "FunctionMISizeChange",
                                          DiagnosticLocation(), &MF->front());
      R << DiagnosticInfoOptimizationBase::Argument("Pass", "Machine Outliner")
        << ": Function: "
        << DiagnosticInfoOptimizationBase::Argument("Function", F.getName())
        << ": MI instruction count changed from "
        << DiagnosticInfoOptimizationBase::Argument("MIInstrsBefore",
                                                    FnCountBefore)
        << " to "
        << DiagnosticInfoOptimizationBase::Argument("MIInstrsAfter",
                                                    FnCountAfter)
        << "; Delta: "
        << DiagnosticInfoOptimizationBase::Argument("Delta", FnDelta);
      return R;
    });
  }
}

bool MachineOutlinerSWH::runOnModule(Module &M) {
  // Check if there's anything in the module. If it's empty, then there's
  // nothing to outline.
  if (M.empty())
    return false;

  // Number to append to the current outlined function.
  // unsigned OutlinedFunctionNum = 0;

  std::string Riscv = M.getTargetTriple();
  if (M.getTargetTriple().rfind("riscv", 0)==0){
//    swh_viewAllCFGModule(M);
    swhDoInterproceduralOutline(M);
//    swh_viewAllCFGModule(M);
  }
  // if (!doOutline(M, OutlinedFunctionNum))
  //   return false;

  return true;
}

bool MachineOutlinerSWH::doOutline(Module &M, unsigned &OutlinedFunctionNum) {
  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfoWrapperPass>().getMMI();

  // If the user passed -enable-machine-outliner=always or
  // -enable-machine-outliner, the pass will run on all functions in the module.
  // Otherwise, if the target supports default outlining, it will run on all
  // functions deemed by the target to be worth outlining from by default. Tell
  // the user how the outliner is running.
  LLVM_DEBUG({
    dbgs() << "Machine Outliner: Running on ";
    if (RunOnAllFunctions)
      dbgs() << "all functions";
    else
      dbgs() << "target-default functions";
    dbgs() << "\n";
  });

  // If the user specifies that they want to outline from linkonceodrs, set
  // it here.
  OutlineFromLinkOnceODRs = true;
    // OutlineFromLinkOnceODRs = EnableLinkOnceODROutlining;
  InstructionMapperSWH Mapper;

  // Prepare instruction mappings for the suffix tree.
  populateMapper(Mapper, M, MMI);
  std::vector<OutlinedFunction> FunctionList;

  // Find all of the outlining candidates.
  findCandidates(Mapper, FunctionList);

  // If we've requested size remarks, then collect the MI counts of every
  // function before outlining, and the MI counts after outlining.
  // FIXME: This shouldn't be in the outliner at all; it should ultimately be
  // the pass manager's responsibility.
  // This could pretty easily be placed in outline instead, but because we
  // really ultimately *don't* want this here, it's done like this for now
  // instead.

  // Check if we want size remarks.
  bool ShouldEmitSizeRemarks = M.shouldEmitInstrCountChangedRemark();
  StringMap<unsigned> FunctionToInstrCount;
  if (ShouldEmitSizeRemarks)
    initSizeRemarkInfo(M, MMI, FunctionToInstrCount);

  // Outline each of the candidates and return true if something was outlined.
  bool OutlinedSomething =
      outline(M, FunctionList, Mapper, OutlinedFunctionNum);

  // If we outlined something, we definitely changed the MI count of the
  // module. If we've asked for size remarks, then output them.
  // FIXME: This should be in the pass manager.
  if (ShouldEmitSizeRemarks && OutlinedSomething)
    emitInstrCountChangedRemark(M, MMI, FunctionToInstrCount);

  LLVM_DEBUG({
    if (!OutlinedSomething)
      dbgs() << "Stopped outlining at iteration " << OutlineRepeatedNum
             << " because no changes were found.\n";
  });

  return OutlinedSomething;
}


void MachineOutlinerSWH::swhDoInterproceduralOutline(Module &M) {
  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfoWrapperPass>().getMMI();
  outliner::SwhCrossBasicBlockOpt Opt;

  Opt.swhPrepareNecessaryInfo(M,MMI);
  Opt.swhCompareRegionsWithFingerprintting();
//
//  for (int i = 0; i < 10; ++i) {
//    opt.testNewFunc(1);
//  }

//  opt.swh_prepareForAbstract();
  Opt.swhDoAbstract();
  errs()<<"\nAll Abstracted!!!\n";
}

//region swh

void SwhCrossBasicBlockOpt::swhPrepareNecessaryInfo(Module &M0, MachineModuleInfo &MMI0){
  M = &M0;
  MMI = &MMI0;

  //first find all functions in the Module
  for (Function &F : *M){
    if (F.empty())
      continue;
    MachineFunction *MF = (*MMI).getMachineFunction(F);
    if (!MF)
      continue;
    if (MF->size()<2){
      continue;
    }

    //构建支配树
    MachineDominatorTree *Mdt = new MachineDominatorTree();
    Mdt->runOnMachineFunction(*MF);
    MachinePostDominatorTree *Mpdt = new MachinePostDominatorTree();
    Mpdt->runOnMachineFunction(*MF);
    SwhNeededMfInfo *NeededMfInfo = new SwhNeededMfInfo();
    NeededMfInfo->swhGetBiDirectionalDominateMatrix(*MF, *Mdt, *Mpdt, NeededMfInfo->BiDirectionalDominateMatrix);
    NeededMfInfo->swhGetNeededRegionsInfo(*MF, NeededRegionsInfo);
    //push each needed machine function's info in to map
    NeededMfInfoMap[MF->getName()]=NeededMfInfo;
  }
}

void
SwhNeededMfInfo::swhGetDominateMatrix(MachineFunction &MF, MachineDominatorTree &MDT, std::vector<std::vector<int>> &Matrix0) {
  int MFSize = MF.size();
  Matrix0 = std::vector<std::vector<int>>(MFSize,std::vector<int>(MFSize,0));
  for (MachineBasicBlock &Mbbx: MF) {
    for (MachineBasicBlock &Mbby: MF) {
      if (MDT.dominates(&Mbbx, &Mbby)){
        Matrix0[Mbbx.getNumber()][Mbby.getNumber()]=1;
      }
    }
  }
//  return matrix;
}


void MachineOutlinerSWH::swhViewAllCFGModule(Module &M) {
  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfoWrapperPass>().getMMI();
  for (Function &F : M) {
    if (F.empty())
      continue;
    MachineFunction *MF = MMI.getMachineFunction(F);
    if (!MF)
      continue;
//    if (MF->size() < 2) {
//      continue;
//    }
    #ifdef __x86_64__
        MF->viewCFG();
    #elif __aarch64__
      MF->viewCFG();
    #endif


  }
}

void SwhNeededMfInfo::swhGetNeededRegionsInfo(MachineFunction &MF, SwhNeededRegionsInfo &NeededRegionsInfo) {
  int DMSize = DominateMatrix.size();
  for (int I = 0; I < DMSize; ++I) {
    for (int J = 0; J < DMSize; ++J) {
      if (I==J ||  BiDirectionalDominateMatrix[I][J]==0)
        continue;
      //block i,j bi-directional dominate each other
      std::vector<int> BlockListOfTheRegion;
      SwhFingerprintConstructor FingerprintConstructor;

      BlockListOfTheRegion.push_back(I);
      BlockListOfTheRegion.push_back(J);
      FingerprintConstructor.BlockCount =2;
      FingerprintConstructor.InstructionCount =0;
      FingerprintConstructor.InstructionCount += MF.getBlockNumbered(I)->size();
      FingerprintConstructor.InstructionCount += MF.getBlockNumbered(J)->size();
      FingerprintConstructor.addBlockPart(0,MF.getBlockNumbered(I)->size());
      FingerprintConstructor.addBlockPart(1,MF.getBlockNumbered(J)->size());



      std::vector<int> IDominatesInfo = DominateMatrix[I];
      std::vector<int> JPostDominatesInfo = PostDominateMatrix[J];
      for (int K = 0; K < DMSize; ++K) {
        if (K!=I && K!=J && IDominatesInfo[K]==1 && JPostDominatesInfo[K]==1){
          BlockListOfTheRegion.push_back(K);
          FingerprintConstructor.BlockCount++;
          FingerprintConstructor.InstructionCount += MF.getBlockNumbered(K)->size();
          FingerprintConstructor.addBlockPart(2,MF.getBlockNumbered(K)->size());
        }
      }
      FingerprintConstructor.addRegionPart(
          FingerprintConstructor.BlockCount,
          FingerprintConstructor.InstructionCount);

      SwhSeseRegion SeseRegion;
//      seseRegion.funcName=MF.getName();
      SeseRegion.ParentFunc=&MF;
      SeseRegion.BlockList = BlockListOfTheRegion;
      SeseRegion.Tag = -1;
      if (!SeseRegion.checkCompleteness()){
        //如果不完整，也就是当前情况是不可抽象的双向支配节点，则跳过
        continue;
      }
      if (!SeseRegion.checkPostCompleteness()){
                //如果不完整，也就是当前情况是不可抽象的双向支配节点，则跳过
        continue;
      }

      std::map<uint64_t ,std::list<SwhSeseRegion>> *RegionsWithFp = &NeededRegionsInfo.RegionsWithFp;
//      std::map<SWH_FingerprintConstructor,std::vector<SwhSeseRegion>> *regionsWithFP = &neededRegionsInfo.regionsWithFP;
      auto Result = RegionsWithFp->find(FingerprintConstructor.Fingerprint);
      if (Result != RegionsWithFp->end()){
        // int Index = std::distance(RegionsWithFp->begin(), Result);

        Result->second.push_back(SeseRegion);
      }
      else{
        std::list<SwhSeseRegion> NewRegionList;
        NewRegionList.push_back(SeseRegion);
        (*RegionsWithFp)[FingerprintConstructor.Fingerprint] = NewRegionList;
      }
    }
  }
}

void SwhCrossBasicBlockOpt::swhCompareRegionsWithFingerprintting() {
  int CurrentTag = 0;
  auto &RegionsWithTag = NeededRegionsInfo.RegionsWithTag;
  for( std::map<uint64_t, std::list<SwhSeseRegion>>::iterator It = NeededRegionsInfo.RegionsWithFp.begin(); It != NeededRegionsInfo.RegionsWithFp.end(); ) {
    if (It->second.size() < 2) {
      //no need to compare
      //note: Both of the following can be right
      //      std::map<uint64_t, std::vector<SwhSeseRegion>>::iterator via = it;
      //      ++it;
      //      neededRegionsInfo.regionsWithFP.erase(via);
      NeededRegionsInfo.RegionsWithFp.erase(It++);
    }
    else
      ++It;
  }

  for(std::map<uint64_t, std::list<SwhSeseRegion>>::iterator Pair = NeededRegionsInfo.RegionsWithFp.begin(); Pair != NeededRegionsInfo.RegionsWithFp.end(); Pair++){
    //取出fingerprint相同的一个桶
    for(std::list<SwhSeseRegion>::iterator I = Pair->second.begin(); I!=Pair->second.end(); I++){
      //取出桶中的第i个元素
      for (std::list<SwhSeseRegion>::iterator J = std::next(I); J!=Pair->second.end(); J++) {
        //取出桶中的第j个元素
        SwhSeseRegion SeseRegion1 = *I;
        SwhSeseRegion SeseRegion2 = *J;

        //region error print
        // i\j进行比较
      //  int a = std::distance(NeededRegionsInfo.RegionsWithFp.begin(), Pair);
      //  if (a == 35){
      //    a = -1;
      //  }
      //  int b = std::distance(Pair->second.begin(), I);
      //  int c = std::distance(Pair->second.begin(), J);
      //  errs()<<"比较桶"<<a<<"中的"<<b<<","<<c<<"元素\n";
        //endregion

        if (SeseRegion1.compareWith(SeseRegion2, *M, *MMI)){
          if (SeseRegion1.Tag==-1 && SeseRegion2.Tag==-1){
            I->Tag = CurrentTag;
            J->Tag = CurrentTag;
            SeseRegion1.Tag=CurrentTag;
            SeseRegion2.Tag=CurrentTag;
            AbstractedFunction *NewAbstractedFunc =new AbstractedFunction();
            NewAbstractedFunc->RegionCandidates.push_back(SeseRegion1);
            NewAbstractedFunc->RegionCandidates.push_back(SeseRegion2);
            NewAbstractedFunc->EndWithPointerToSelfRegion =
                SeseRegion1.isEndWithPointerToSelf();
//            newAbstractedFunc.ContainsCall = seseRegion1.isContainsCall();
            RegionsWithTag[CurrentTag] = *NewAbstractedFunc;
            CurrentTag++;
          }
          else if (SeseRegion2.Tag==-1){
            J->Tag=SeseRegion1.Tag;
            SeseRegion2.Tag=SeseRegion1.Tag;
            RegionsWithTag[SeseRegion1.Tag].RegionCandidates.push_back(SeseRegion2);
          }
          else if (SeseRegion1.Tag==-1){
            I->Tag=SeseRegion2.Tag;
            SeseRegion1.Tag=SeseRegion2.Tag;
            RegionsWithTag[SeseRegion2.Tag].RegionCandidates.push_back(SeseRegion1);
          }
        }
      }
    }
  }
}

void SwhCrossBasicBlockOpt::swhPrepareForAbstract() {
  std::map<int,AbstractedFunction> &TagAbstractedFunctionMap = NeededRegionsInfo.RegionsWithTag;
  for( std::map<int,AbstractedFunction>::iterator It = TagAbstractedFunctionMap.begin(); It != TagAbstractedFunctionMap.end(); ) {
    const TargetInstrInfo &TII = *It->second.RegionCandidates.begin()->ParentFunc->getSubtarget().getInstrInfo();
    //can abstract? in which way? benefit?
    TII.getAbstractingCandidateInfo(It->second);
    if (It->second.AbstractingID==3 || It->second.AbstractedBenefit<1) {
      TagAbstractedFunctionMap.erase(It++);
    }
    else{
      ++It;
    }

  }

}

void SwhCrossBasicBlockOpt::swhDoAbstract() {

  std::map<int,AbstractedFunction> &TagAbstractedFunctionMap = NeededRegionsInfo.RegionsWithTag;
  //TODO: abstracted by benefit count
  for( std::map<int,AbstractedFunction>::iterator It = TagAbstractedFunctionMap.begin(); It != TagAbstractedFunctionMap.end(); ) {

    //保留旧的去重标准
    auto OldAbstractedBlocks = AbstractedBlocks;
    //去重
    // If we outlined something that overlapped with a candidate in a previous
    // step, then we can't outline from it.
    if (haveAbstractedPartOf(It->second)){
      //rm rwt
      TagAbstractedFunctionMap.erase(It++);
      continue;
    }

    //优先做一些必要的检查
    const TargetInstrInfo &TII = *It->second.RegionCandidates.begin()->ParentFunc->getSubtarget().getInstrInfo();
    //can abstract? in which way? benefit?
    TII.getAbstractingCandidateInfo(It->second);

    //如果不满足要求，则删除对应项
    if (It->second.AbstractingID==3 || It->second.AbstractedBenefit<1) {
      TagAbstractedFunctionMap.erase(It++);
      // errs()<<"\nlast insert fail!";
      AbstractedBlocks = OldAbstractedBlocks;
      continue;
    }

    if (It->second.EndWithPointerToSelfRegion && It->second.EndWithMoreThanOneTerminator){
      //如果同时触发两种特殊情况，暂时不处理
      TagAbstractedFunctionMap.erase(It++);
      // errs()<<"\nlast insert fail!";
      AbstractedBlocks = OldAbstractedBlocks;
      continue;
    }

    auto &RWT=*It;
    //满足所有判断后，打印输出
    RWT.second.emitMark();

    std::list<SwhSeseRegion> &RegionCandidates = RWT.second.RegionCandidates;
    MachineFunction &MF = *swhCreateAbstractFunction(RWT.first,RWT.second);
    FunctionsCreated++;

    for (SwhSeseRegion Region:RegionCandidates){
      MachineBasicBlock &StartBlock = *Region.ParentFunc->getBlockNumbered(Region.BlockList[0]);
      MachineBasicBlock::iterator StartIt = StartBlock.front();
      MachineBasicBlock::iterator EndIt = StartBlock.back();
      //先删除节点间的关系
      MachineBasicBlock &EndBlock = *Region.ParentFunc->getBlockNumbered(Region.BlockList[1]);
      //start block清除所有succ
      // for (MachineBasicBlock *Succ : StartBlock.successors()) {
      //   if (Succ->getNumber()<0)
      //     break;
      //   StartBlock.removeSuccessor(Succ);
      // }
      while (!StartBlock.succ_empty()){
        MachineBasicBlock &Succ = **StartBlock.succ_begin();
        if (Succ.getNumber()<0)
          break;
        if (StartBlock.isSuccessor(&Succ)){
          StartBlock.removeSuccessor(&Succ);
        }
      }
      //endblock移除所有predecessors
      while (!EndBlock.pred_empty()){
        MachineBasicBlock &Pred = **EndBlock.pred_begin();
        if (Pred.isSuccessor(&EndBlock))
          Pred.removeSuccessor(&EndBlock);
      }
      //startblock移除所有来自内部的predecessors
//      for (int blockNum:region.blockList){
//        MachineBasicBlock &MBB = *region.parentFunc->getBlockNumbered(blockNum);
//        if (MBB.isSuccessor(&StartBlock)){
//          MBB.removeSuccessor(&StartBlock);
//        }
//      }

//      for (std::vector<MachineBasicBlock *>::iterator pred=StartBlock.pred_begin(); pred!=StartBlock.pred_end();) {
//        if (StartBlock.pred_empty()){
//          break;
//        }
//        std::vector<MachineBasicBlock *>::iterator next = std::next(pred);
//        if(!(*pred) || !(**pred).getSublistAccess(NULL) || !(**pred).getSublistAccess(NULL))
//          break;;
//        MachineBasicBlock &predPointer = **pred;
//        if (!predPointer.getParent())
//          break;
//        predPointer.dump();
//        if (!predPointer.getSublistAccess(nullptr))
//          break;
//        if (predPointer.size()<=0|| predPointer.getNumber()<0)
//          break;
//        if (region.listContains(region.blockList, predPointer.getNumber()) && predPointer.isSuccessor(&StartBlock))
//          predPointer.removeSuccessor(&StartBlock);
//        pred = next;
//      }
      for (auto *Pred:StartBlock.predecessors()) {
        if (Pred->getNumber()<0)
          break;
        if (Region.listContains(Region.BlockList, Pred->getNumber()) && Pred->isSuccessor(&StartBlock))
          Pred->removeSuccessor(&StartBlock);
      }
      //endblock移除所有指向内部的successors
      for (auto *Succ:EndBlock.successors()) {
        if (Succ->getNumber()<0)
          break;
        if (Region.listContains(Region.BlockList, Succ->getNumber()))
        EndBlock.removeSuccessor(Succ);
      }

      //而后在插入call指令并删除
      auto CallInst = TII.insertAbstractedCall(*M, StartBlock, StartIt, MF, Region);
      //检查生命周期
      if (StartBlock.getParent()->getProperties().hasProperty(
          MachineFunctionProperties::Property::TracksLiveness)) {
        SmallSet<Register, 2> UseRegs, DefRegs;
        for (MachineBasicBlock::reverse_iterator
                 Iter = EndIt.getReverse(),
                 Last = std::next(CallInst.getReverse());
             Iter != Last; Iter++) {
          MachineInstr *MI = &*Iter;
          for (MachineOperand &MOP : MI->operands()) {
            if (!MOP.isReg())
              continue;

            if (MOP.isDef()) {
              DefRegs.insert(MOP.getReg());
              if (UseRegs.count(MOP.getReg()))
                UseRegs.erase(MOP.getReg());
            } else if (!MOP.isUndef()) {
              UseRegs.insert(MOP.getReg());
            }
          }
          if (MI->isCandidateForCallSiteEntry())
            MI->getMF()->eraseCallSiteInfo(MI);
        }
        for (const Register &I : DefRegs)
          CallInst->addOperand(
              MachineOperand::CreateReg(I, true, /* isDef = true */
                                        true /* isImp = true */));

        for (const Register &I : UseRegs)
          CallInst->addOperand(
              MachineOperand::CreateReg(I, false, /* isDef = false */
                                        true /* isImp = true */));
      }

      StartBlock.erase(std::next(StartIt), std::next(EndIt));

      //TODO 延迟移除
      //将中间的block移除
      for (unsigned I = 2; I<Region.BlockList.size();I++){
        Region.ParentFunc->erase(Region.ParentFunc->getBlockNumbered(Region.BlockList[I]));
      }

      if (RWT.second.EndWithPointerToSelfRegion){
        //这种情况不保留end block
        for (MachineBasicBlock *Succ : EndBlock.successors()) {
          if (!Region.listContains(Region.BlockList, Succ->getNumber())){
            StartBlock.addSuccessor(Succ);
          }
          EndBlock.removeSuccessor(Succ);
        }
        Region.ParentFunc->erase(&EndBlock);
      } else {
        //这种情况end block保留最后一个指令，并且将其添加为begin block的successor
        EndBlock.erase(EndBlock.begin(),EndBlock.back());
        StartBlock.addSuccessor(&EndBlock);
        for (MachineBasicBlock *Succ : EndBlock.successors()) {
          if (Region.listContains(Region.BlockList, Succ->getNumber()))
            EndBlock.removeSuccessor(Succ);
        } // end if else

      } //end  for(SwhSeseRegion region:RegionCandidates)

    }

    ++It;
  }

}

//endregion
//endregion

void checkSucc(AbstractedFunction AF){
  int Mmviahsv = 0;
  for (SwhSeseRegion Candidate:AF.RegionCandidates){
    if (Mmviahsv==0){
      Mmviahsv++;
      continue;
    }
    Candidate.ParentFunc->print(errs());
    Candidate.ParentFunc->viewCFG();
    errs()<<Candidate.ParentFunc->getName();
    errs()<<":\n";
    for (unsigned long I = 0; I < Candidate.BlockList.size(); ++I) {
      MachineBasicBlock &MBB = *Candidate.ParentFunc->getBlockNumbered(Candidate.BlockList[I]);
      for (MachineBasicBlock *Succ :MBB.successors()) {
        if (Succ->getNumber()<0){
          errs()<<"error";
        }
        errs()<<MBB.getNumber();
        errs()<<"->";
        errs()<<Succ->getNumber();
        errs()<<"\n";
      }
    }
  }
}

MachineFunction *SwhCrossBasicBlockOpt::swhCreateAbstractFunction(unsigned Name, AbstractedFunction &AF) {
  std::string FunctionName = "ABSTRACT_FUNCTION_";
  FunctionName += std::to_string(Name);
  // Create the function using an IR-level function.
  LLVMContext &C = M->getContext();
  Function *F = Function::Create(FunctionType::get(Type::getVoidTy(C), false),
                                 Function::ExternalLinkage, FunctionName, M);
  SwhSeseRegion &FirstCand=*AF.RegionCandidates.begin();
  const Function &ParentFn =AF.RegionCandidates.begin()->ParentFunc->getFunction();
  //TODO: to add all parents to check
  if (ParentFn.hasFnAttribute("target-features")){
    Attribute Attribute = ParentFn.getFnAttribute("target-features");
    // StringRef Str0 = Attribute.getAsString();
    F->addFnAttr(Attribute);
  }

  F->setLinkage(GlobalValue::InternalLinkage);
  F->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
  F->addFnAttr(Attribute::OptimizeForSize);
  F->addFnAttr(Attribute::MinSize);

  // Include target features from an arbitrary candidate for the outlined
  // function. This makes sure the outlined function knows what kinds of
  // instructions are going into it. This is fine, since all parent functions
  // must necessarily support the instructions that are in the outlined region.
//  for (auto regionWithTag:neededRegionsInfo.regionsWithTag) {
//
//  }




  // Set nounwind, so we don't generate eh_frame.
  if (llvm::all_of(AF.RegionCandidates,[](const SwhSeseRegion &Region) {
    return Region.ParentFunc->getFunction().hasFnAttribute(Attribute::NoUnwind);
  }))
    F->addFnAttr(Attribute::NoUnwind);

  //为这一Function创建多个Block
  BasicBlock *EntryBB = BasicBlock::Create(C, "entry", F);
  IRBuilder<> Builder(EntryBB);
  Builder.CreateRetVoid();
  //for循环遍历，对于SESERegion中的每个Block,都添加到新的Function中


  MachineFunction &MF = MMI->getOrCreateMachineFunction(*F);
  const TargetSubtargetInfo &STI = MF.getSubtarget();
  const TargetInstrInfo &TII = *STI.getInstrInfo();
  MachineFunction *OriginalMF = FirstCand.ParentFunc;
  const std::vector<MCCFIInstruction> &Instrs = OriginalMF->getFrameInstructions();

  FirstCand.toMachineFunction(MF, STI, TII, Instrs,
                              AF.EndWithPointerToSelfRegion,
                              AF.EndWithMoreThanOneTerminator);

  //region 对MF的属性进行设置
  // Set normal properties for a late MachineFunction.
  MF.getProperties().reset(MachineFunctionProperties::Property::IsSSA);
  MF.getProperties().set(MachineFunctionProperties::Property::NoPHIs);
  MF.getProperties().set(MachineFunctionProperties::Property::NoVRegs);
  MF.getProperties().set(MachineFunctionProperties::Property::TracksLiveness);
  MF.getRegInfo().freezeReservedRegs(MF);
  //endregion


  //region 处理存活寄存器,
  // Compute live-in set for outlined fn
  const MachineRegisterInfo &MRI = MF.getRegInfo();
  const TargetRegisterInfo &TRI = *MRI.getTargetRegisterInfo();
  //统计整个Region中的liveins
  LivePhysRegs LiveInRegions(TRI);
  for (unsigned long I = 0; I < FirstCand.BlockList.size(); ++I) {
    LivePhysRegs LiveIns(TRI);
    for (auto &Cand : AF.RegionCandidates) {
      MachineBasicBlock &OutlineBB = *Cand.ParentFunc->getBlockNumbered(Cand.BlockList[I]);
      LivePhysRegs CandLiveIns(TRI);
      CandLiveIns.addLiveOuts(OutlineBB);
      for (const MachineInstr &MI :
          reverse(make_range(OutlineBB.begin(), OutlineBB.end())))
        CandLiveIns.stepBackward(MI);
      for (MCPhysReg Reg : make_range(CandLiveIns.begin(), CandLiveIns.end()))
        LiveIns.addReg(Reg);
    }
    addLiveIns(*MF.getBlockNumbered(I), LiveIns);
    //统计整个Region中的liveins
    for (MCPhysReg Reg:LiveIns) {
      LiveInRegions.addReg(Reg);
    }
  }
  //endregion

  //添加ret
  AF.MF = &MF;
  TII.buildAbstractedFrame(*AF.getEndMachineBasicBlock(), MF, AF);


  //region 处理DISubprogram所需的信息，已注释
  // If there's a DISubprogram associated with this outlined function, then
  // emit debug info for the outlined function.
//  if (DISubprogram *SP = swh_getSubprogramOrNull(AF)) {
//    // We have a DISubprogram. Get its DICompileUnit.
//    DICompileUnit *CU = SP->getUnit();
//    DIBuilder DB(*M, true, CU);
//    DIFile *Unit = SP->getFile();
//    Mangler Mg;
//    // Get the mangled name of the function for the linkage name.
//    std::string Dummy;
//    llvm::raw_string_ostream MangledNameStream(Dummy);
//    Mg.getNameWithPrefix(MangledNameStream, F, false);
//
//    DISubprogram *OutlinedSP = DB.createFunction(
//        Unit /* Context */, F->getName(), StringRef(MangledNameStream.str()),
//        Unit /* File */,
//        0 /* Line 0 is reserved for compiler-generated code. */,
//        DB.createSubroutineType(DB.getOrCreateTypeArray(None)), /* void type */
//        0, /* Line 0 is reserved for compiler-generated code. */
//        DINode::DIFlags::FlagArtificial /* Compiler-generated code. */,
//        /* Outlined code is optimized code by definition. */
//        DISubprogram::SPFlagDefinition | DISubprogram::SPFlagOptimized);
//
//    // Don't add any new variables to the subprogram.
//    DB.finalizeSubprogram(OutlinedSP);
//
//    // Attach subprogram to the function.
//    F->setSubprogram(OutlinedSP);
//    // We're done with the DIBuilder.
//    DB.finalize();
//  }

  //endregion

  // TODO: to deal with the jump table
  // MachineJumpTableInfo *JTI = MF.getJumpTableInfo();
  // JTI = MMI->getMachineFunction(ParentFn)->getJumpTableInfo();

  return &MF;
}

bool SwhCrossBasicBlockOpt::haveAbstractedPartOf(
    AbstractedFunction &AF) {
  auto AbstractedBlocksVia = AbstractedBlocks;
  for (std::list<SwhSeseRegion>::iterator R = AF.RegionCandidates.begin(); R!=AF.RegionCandidates.end();){
    MachineFunction *MF = R->ParentFunc;
    auto Abvia = AbstractedBlocksVia;
    bool HaveRepeat = false;
    for (int I:R->BlockList){
      if (!Abvia.insert(std::make_pair(MF, I)).second)
      {
        HaveRepeat = true;
        break;
      }
    }
    if (HaveRepeat){
      //remove R from the RegionCandidates list
      AF.RegionCandidates.erase(R++);
    }
    else{
      AbstractedBlocksVia = Abvia;
      ++R;
    }
  }
  if (AF.RegionCandidates.size()<2){
    return true;
  }
  AbstractedBlocks = AbstractedBlocksVia;
  return false;

}

void SwhCrossBasicBlockOpt::testNewFunc(int A) {
  std::string FunctionName = "Test_FUNCTION_";
  FunctionName += std::to_string(std::time(0));
  LLVMContext &C = M->getContext();

  if (A ==1){
    AbstractedFunction &AF = NeededRegionsInfo.RegionsWithTag.begin()->second;
    Function *F = Function::Create(FunctionType::get(Type::getVoidTy(C), false),
                                   Function::ExternalLinkage, FunctionName, M);
    // SwhSeseRegion &FirstCand=
    //     const_cast<SwhSeseRegion &>(*(AF.RegionCandidates.begin()));
    const Function &ParentFn =AF.RegionCandidates.begin()->ParentFunc->getFunction();
    if (ParentFn.hasFnAttribute("target-features")){
      Attribute MyAttribute = ParentFn.getFnAttribute("target-features");
      // StringRef Str1 = MyAttribute.getAsString();
      F->addFnAttr(MyAttribute);
    }
    F->setLinkage(GlobalValue::InternalLinkage);
    F->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    F->addFnAttr(Attribute::OptimizeForSize);
    F->addFnAttr(Attribute::MinSize);
    F->addFnAttr(Attribute::NoUnwind);
  }
  else if (A == 0){
    Function *F = Function::Create(FunctionType::get(Type::getVoidTy(C), false),
                                   Function::ExternalLinkage, FunctionName, M);
    SwhSeseRegion &FirstCand = *NeededRegionsInfo.RegionsWithFp.begin()->second.begin();
    const Function &ParentFn =FirstCand.ParentFunc->getFunction();
    if (ParentFn.hasFnAttribute("target-features")){
      Attribute MyAttribute = ParentFn.getFnAttribute("target-features");
      // StringRef Str0 = MyAttribute.getAsString();
      F->addFnAttr(MyAttribute);
    }
    F->setLinkage(GlobalValue::InternalLinkage);
    F->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    F->addFnAttr(Attribute::OptimizeForSize);
    F->addFnAttr(Attribute::MinSize);
    F->addFnAttr(Attribute::NoUnwind);
  }




}
