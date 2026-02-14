From Stdlib Require Import String List ZArith Zmod Bool.
Require Import Guru.Syntax Guru.Notations Guru.Semantics Guru.Library.
Require Import Cheriot.Alu Cheriot.Switcher.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Spec.
  Variable MemWidth: nat.
  Definition LgBytesFullCapSz := Eval compute in Z.to_nat LgNumBytesFullCapSz.
  Variable MemWidthGeLgBytesFullCapSz: MemWidth >= LgBytesFullCapSz.
  Definition MemByteSz := Nat.pow 2 MemWidth.
  Definition MemFullCapSz := Nat.pow 2 (MemWidth - LgBytesFullCapSz).
  Definition switcherLength := Eval compute in (length switcher).
  Definition specInst: type (Array switcherLength (Bit 8)) := Build_SameTuple (tupleElems := switcher)
                                                                (I: Is_true (length switcher =? switcherLength)).
  Variable memInit: type (Array MemByteSz (Bit 8)).
  Definition waits := Default (Array NumRegs Bool).
  Variable scrsInit: type Scrs.

  Variable RevStart: Z.
  Variable RevByteSz: Z.
  Variable RevEachBitLgNumBytes: Z.
  Variable RevEachBitLgNumBytesInMem: (RevEachBitLgNumBytes < Z.of_nat MemWidth)%Z.
  Variable RevInMem: (RevStart + RevByteSz < Z.of_nat MemByteSz)%Z.
  Variable HeapStart: Z.
  Definition HeapEnd := (HeapStart + (RevByteSz * (Z.shiftl 1 RevEachBitLgNumBytes) * 8))%Z.
  Variable HeapInMem: (HeapEnd < Z.of_nat MemByteSz)%Z.
  Variable RevokerAddr: Z.
  Definition RevokerSize: Z := 4.
  Definition LgRevokerSzBytes: Z := Z.log2_up XlenBytes + Z.log2_up RevokerSize.

  Definition RevStartAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ RevStart.
  Definition HeapStartAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ HeapStart.
  Definition HeapEndAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ HeapEnd.

  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Definition MemWidthCap : Z := Z.of_nat MemWidth - LgNumBytesFullCapSz.

  Definition specRegs := [("mem", Build_Reg _ memInit);
                          ("tags", Build_Reg _ (Default (Array MemFullCapSz Bool)));
                          ("regs", Build_Reg _ (Default (Array NumRegs FullECapWithTag)));
                          ("csrs", Build_Reg _ (Default Csrs));
                          ("scrs", Build_Reg _ scrsInit);
                          ("interrupts", Build_Reg _ (Default Interrupts));
                          ("revokerEpoch", Build_Reg _ (Default Data));
                          ("revokerKick", Build_Reg _ (Default Bool));
                          ("revokerStart", Build_Reg _ (Default (Bit MemWidthCap)));
                          ("revokerEnd", Build_Reg _ (Default (Bit MemWidthCap)));
                          ("revokeAddr", Build_Reg _ (Default (Bit MemWidthCap)))].

  Definition SpecRevokerAccessState := STRUCT_TYPE {
                                           "revokerEpoch" :: Data;
                                           "revokerKick" :: Bool;
                                           "revokerStart" :: Bit MemWidthCap;
                                           "revokerEnd" :: Bit MemWidthCap }.

  Definition SpecProcessorState := STRUCT_TYPE {
                                       "mem" :: Array MemByteSz (Bit 8);
                                       "tags" :: Array MemFullCapSz Bool;
                                       "regs" :: Array NumRegs FullECapWithTag;
                                       "csrs" :: Csrs;
                                       "scrs" :: Scrs;
                                       "interrupts" :: Interrupts;
                                       "revokerAccess" :: SpecRevokerAccessState }.

  Definition specDecl: ModDecl := {|modRegs := specRegs;
                                    modMems := nil;
                                    modRegUs := nil;
                                    modMemUs := nil;
                                    modSends := [("pcOut", Addr)];
                                    modRecvs := [("interrupts", Interrupts)]|}.
  Local Close Scope string_scope.

  Definition specLists := getModLists specDecl.

  Section Ty.
    Variable ty: Kind -> Type.

    Definition RevokerEpochAddr: Expr ty Addr := $(RevokerAddr + XlenBytes*0).
    Definition RevokerKickAddr: Expr ty Addr  := $(RevokerAddr + XlenBytes*1).
    Definition RevokerStartAddr: Expr ty Addr := $(RevokerAddr + XlenBytes*2).
    Definition RevokerEndAddr: Expr ty Addr   := $(RevokerAddr + XlenBytes*3).
    
    Definition isInHeap (addr: ty (Bit (AddrSz + 1))): Expr ty Bool :=
      And [Sge #addr (ConstBit HeapStartAddr); Slt #addr (ConstBit HeapEndAddr)].

    Definition revBitNum (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit (AddrSz + 1)) :=
      Srl (Sub #addr (ConstBit HeapStartAddr)) (ConstBit (bits.of_Z (Z.of_nat MemWidth) RevEachBitLgNumBytes)).

    Definition revBitByteAddr (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit (AddrSz + 1)) :=
      Srl (revBitNum addr) (ConstBit (bits.of_Z 2 3)).

    Definition revBitByteOffset (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit 3) :=
      TruncLsb ((AddrSz + 1) - 3) 3 (revBitNum addr).

    Definition isRevokerAddr (a: ty Addr) (sz: ty (Bit MemSz)) :=
      And [Sge #a RevokerEpochAddr; Slt #a RevokerEndAddr; Eq #sz $XlenBytes ].

    Definition getRevokerOffset (a: ty Addr): Expr ty (Bit (Z.log2_up RevokerSize)) :=
      TruncMsb (Z.log2_up RevokerSize) (Z.log2_up XlenBytes)
        (TruncLsb (AddrSz - LgRevokerSzBytes) LgRevokerSzBytes (Sub #a RevokerEpochAddr)).

    Definition readRevoker (offset: ty (Bit (Z.log2_up RevokerSize))) (revokerState: ty SpecRevokerAccessState):
      Expr ty Data :=
      (Or [ITE0 (Eq #offset $0) ##revokerState`"revokerEpoch";
           ITE0 (Eq #offset $1) (Const ty Data (bits.of_Z _ 0));
           ITE0 (Eq #offset $2) (castBits (Zplus_minus _ _)
                                   (ZeroExtendTo AddrSz ##revokerState`"revokerStart"));
           ITE0 (Eq #offset $3) (castBits (Zplus_minus _ _)
                                   (ZeroExtendTo AddrSz ##revokerState`"revokerEnd"))]).

    Definition getRevokerAddr (a: ty Addr): Expr ty (Bit MemWidthCap).
      refine
        (TruncMsb MemWidthCap LgNumBytesFullCapSz
           (castBits _ (TruncLsb (AddrSz - Z.of_nat MemWidth) (Z.of_nat MemWidth) (castBits _ #a)))).
      - abstract (unfold MemWidthCap; lia).
      - abstract (unfold AddrSz; lia).
    Defined.

    Definition writeRevoker (offset: ty (Bit (Z.log2_up RevokerSize))) (d: ty Data) (old: ty SpecRevokerAccessState)
      : Expr ty SpecRevokerAccessState :=
      STRUCT {
          "revokerEpoch" ::= ITE (Eq #offset $0) #d ##old`"revokerEpoch";
          "revokerKick" ::= Eq #offset $1;
          "revokerStart" ::= ITE (Eq #offset $2) (getRevokerAddr d) #old`"revokerStart";
          "revokerEnd" ::= ITE (Eq #offset $3) (getRevokerAddr d) #old`"revokerEnd"
        }.

    Section LetExpr.
      Variable state: ty SpecProcessorState.

      Ltac specSimpl x :=
        (let y := eval cbv [getFinStruct structList arraySize fieldK forceOption getFinStructOption length
                              fst snd String.eqb Ascii.eqb Bool.eqb fieldNameK nth_pf finNum] in x in
           simplKind y).

      Notation specSimpl x := ltac:(specSimpl x) (only parsing).

      Definition stepExpr: LetExpr ty SpecProcessorState := specSimpl
        ( LetE insts : Array switcherLength (Bit 8) <- Const ty _ specInst;
          LetE mem <- ##state`"mem";
          LetE tags <- ##state`"tags";
          LetE regs <- ##state`"regs";
          LetE csrs <- ##state`"csrs";
          LetE scrs <- ##state`"scrs";
          LetE interrupts <- ##state`"interrupts";
          LetE revoker <- ##state`"revokerAccess";
          LetE pcc : FullECapWithTag <- #regs $[ 0 ];
          LetE pcVal : Addr <- #pcc`"addr";
          LetE BoundsException : Bool <- And [Slt (ZeroExtend 1 #pcVal) (##pcc`"ecap"`"top")];
          LetE pcAluOut: PcAluOut <- STRUCT { "pcVal" ::= #pcVal;
                                              "BoundsException" ::= #BoundsException };
          LetE inst: Inst <- ToBit (slice #insts #pcVal (Z.to_nat InstSz/8));
          LETE decodeOut: DecodeOut <- decode inst;
          
          LetE aluIn: AluIn <- STRUCT { "pcAluOut" ::= #pcAluOut;
                                        "decodeOut" ::= #decodeOut;
                                        "regs" ::= #regs;
                                        "waits" ::= Const ty _ waits;
                                        "csrs" ::= #csrs;
                                        "scrs" ::= #scrs;
                                        "interrupts" ::= #interrupts };
          LetE pcTag <- #pcc`"tag";
          LetE pcCap <- #pcc`"ecap";
          LETE aluOut: AluOut <- alu pcTag pcCap aluIn;
          LetE memAddr: Addr <- ##aluOut`"multicycleOp"`"memAddr";
          LetE memSz: Bit MemSz <- Sll $1 (##aluOut`"multicycleOp"`"memSz");
          LetE isCap: Bool <- isZero #memSz;
          LetE ldUn: Bool <- ##aluOut`"multicycleOp"`"LoadUnsigned";

          LetE isRevoker: Bool <- isRevokerAddr memAddr memSz;
          LetE revokerOffset: Bit (Z.log2_up RevokerSize) <- getRevokerOffset memAddr;
          LetE revokerData: Data <- readRevoker revokerOffset revoker;

          LetE bytes: Array _ (Bit 8) <- slice #mem #memAddr (Z.to_nat DXlenBytes);
          LetE fullCap <- FromBit FullCap (ToBit #bytes);
          LetE ldCap: Cap <- #fullCap`"cap";
          LetE ldVal <- FromBit (Array (Z.to_nat XlenBytes) (Bit 8)) (ITE #isRevoker #revokerData #fullCap`"addr");
          LetE ldValFinal <- ToBit (ITE #ldUn (ArrayZeroExtend #memSz #ldVal) (ArraySignExtend #memSz #ldVal));
          LETE ldECap: ECap <- decodeCap ldCap ldValFinal;
          LetE ldECapFinal: ECap <- ITE #isCap #ldECap ConstDef;
          LetE memTagAddr: Bit (AddrSz - MemSz) <- TruncMsb _ MemSz #memAddr;
          LetE ldTag: Bool <- #tags@[#memTagAddr];
          LetE ldBase: Bit (AddrSz + 1) <- #ldECap`"base";
          LetE revByte: Array 8 Bool <- FromBit (Array 8 Bool) #mem@[revBitByteAddr ldBase];
          LetE revBit: Bool <- #revByte@[revBitByteOffset ldBase];
          LetE ldTagFinal: Bool <- ITE #isCap (And [#ldTag; Not #revBit]) ConstDef;
          LetE ldFinal: FullECapWithTag <- STRUCT { "tag" ::= #ldTagFinal;
                                                    "ecap" ::= #ldECapFinal;
                                                    "addr" ::= #ldValFinal };

          LetE ldRegIdx <- ##aluOut`"multicycleOp"`"loadRegIdx";
          LetE aluOutRegs: Array NumRegs FullECapWithTag <- ##aluOut`"regs";
          LetE newRegs: Array NumRegs FullECapWithTag <- #aluOutRegs
                                                           @[ #ldRegIdx <- ITE (##aluOut`"multicycleOp"`"Load")
                                                                             #ldFinal
                                                                             (#aluOutRegs@[#ldRegIdx])];

          LetE stECap: ECap <- ##aluOut`"multicycleOp"`"storeVal"`"ecap";

          LetE stVal <- ##aluOut`"multicycleOp"`"storeVal"`"addr";
          LETE stCap: Cap <- encodeCap stECap;
          LetE stBits: Bit DXlen <- {< ToBit #stCap, #stVal >};
          LetE stBytes: Array (Z.to_nat DXlenBytes) (Bit 8) <- FromBit _ #stBits;
          LetE Store: Bool <- ##aluOut`"multicycleOp"`"Store";
          LetE StoreMem: Bool <- And [#Store; Not #isRevoker];
          LetE newRevoker <- ITE (And [#Store; #isRevoker])
                                   (writeRevoker revokerOffset stVal revoker)
                                   #revoker;

          LETE updMem <- updSlice #mem #memAddr #stBytes #memSz;

          LetE newMem <- ITE #StoreMem #updMem #mem;
          LetE newTags: Array MemFullCapSz Bool <- #tags
                                                     @[#memTagAddr <- ITE (And [#isCap; #StoreMem])
                                                                        (##aluOut`"multicycleOp"`"storeVal"`"tag")
                                                                        #ldTag];

          @RetE _ SpecProcessorState (STRUCT { "mem" ::= #newMem;
                                               "tags" ::= #newTags;
                                               "regs" ::= #newRegs;
                                               "csrs" ::= #aluOut`"csrs";
                                               "scrs" ::= ##aluOut`"scrs";
                                               "interrupts" ::= ##aluOut`"interrupts";
                                               "revokerAccess" ::= #newRevoker })).
    End LetExpr.

    Definition interrupts: Action ty (getModLists specDecl) (Bit 0) :=
      ( Get interrupts <- "interrupts" in specLists;
        RegRead specInterrupts <- "interrupts" in specLists;
        RegWrite "interrupts" in specLists <- Or [#interrupts; #specInterrupts];
        Retv ).

    Definition step: Action ty (getModLists specDecl) (Bit 0) :=
      ( RegRead mem <- "mem" in specLists;
        RegRead tags <- "tags" in specLists;
        RegRead regs <- "regs" in specLists;
        RegRead csrs <- "csrs" in specLists;
        RegRead scrs <- "scrs" in specLists;
        RegRead interrupts <- "interrupts" in specLists;
        RegRead revokerEpoch <- "revokerEpoch" in specLists;
        RegRead revokerKick <- "revokerKick" in specLists;
        RegRead revokerStart <- "revokerStart" in specLists;
        RegRead revokerEnd <- "revokerEnd" in specLists;

        Let revoker : SpecRevokerAccessState <- STRUCT { "revokerEpoch" ::= #revokerEpoch;
                                                         "revokerKick" ::= #revokerKick;
                                                         "revokerStart" ::= #revokerStart;
                                                         "revokerEnd" ::= #revokerEnd };
        Let fullState: SpecProcessorState <- STRUCT { "mem" ::= #mem;
                                                      "tags" ::= #tags;
                                                      "regs" ::= #regs;
                                                      "csrs" ::= #csrs;
                                                      "scrs" ::= #scrs;
                                                      "interrupts" ::= #interrupts;
                                                      "revokerAccess" ::= #revoker };
        LetL updRegs : SpecProcessorState <- stepExpr fullState;

        Put "pcOut" in specLists <- #regs $[0]`"addr";

        RegWrite "mem" in specLists <- #updRegs`"mem";
        RegWrite "tags" in specLists <- ##updRegs`"tags";
        RegWrite "regs" in specLists <- ##updRegs`"regs";
        RegWrite "csrs" in specLists <- ##updRegs`"csrs";
        RegWrite "scrs" in specLists <- ##updRegs`"scrs";
        RegWrite "interrupts" in specLists <- ##updRegs`"interrupts";
        RegWrite "revokerEpoch" in specLists <- ##updRegs`"revokerAccess"`"revokerEpoch";
        RegWrite "revokerKick" in specLists <- ##updRegs`"revokerAccess"`"revokerKick";
        RegWrite "revokerStart" in specLists <- ##updRegs`"revokerAccess"`"revokerStart";
        RegWrite "revokerEnd" in specLists <- ##updRegs`"revokerAccess"`"revokerEnd";
        Retv ).

    Definition RevokerUpdState := STRUCT_TYPE {
                                      "tags" :: Array MemFullCapSz Bool;
                                      "revokerEpoch" :: Data;
                                      "revokerKick" :: Bool;
                                      "revokeAddr" :: Bit MemWidthCap }.

    Section LetExpr.
      Variable mem: ty (Array MemByteSz (Bit 8)).
      Variable revokerStart: ty (Bit MemWidthCap).
      Variable revokerEnd: ty (Bit MemWidthCap).
      Variable revokerUpdState: ty RevokerUpdState.

      Definition revokerExpr: LetExpr ty RevokerUpdState :=
        ( LetE tags <- #revokerUpdState`"tags";
          LetE revokerEpoch <- #revokerUpdState`"revokerEpoch";
          LetE revokerKick <- #revokerUpdState`"revokerKick";
          LetE revokeAddr <- #revokerUpdState`"revokeAddr";
          LetE ldTag <- #tags@[#revokeAddr];
          LetE bytes <- slice #mem {< #revokeAddr, ConstBit (bits.of_Z MemSz 0) >} (Z.to_nat DXlenBytes);
          LetE fullCap <- FromBit FullCap (ToBit #bytes);
          LetE ldCap <- #fullCap`"cap";
          LetE ldVal <- #fullCap`"addr";
          LETE ldECap: ECap <- decodeCap ldCap ldVal;
          LetE ldBase <- #ldECap`"base";
          LetE revByte: Array 8 Bool <- FromBit (Array 8 Bool) #mem@[revBitByteAddr ldBase];
          LetE revBit: Bool <- #revByte@[revBitByteOffset ldBase];
          LetE ldTagFinal <- And [#ldTag; Not #revBit];
          LetE newTags: Array MemFullCapSz Bool <- #tags@[#revokeAddr <- #ldTagFinal];

          LetE workStart <- And [Eq ##revokeAddr ##revokerEnd; #revokerKick];
          LetE doWork <- Slt #revokeAddr #revokerEnd;
          LetE incRevokeAddr <- Add [#revokeAddr; $1];
          LetE newRevokeAddr <- ITE #workStart
                                  #revokerStart
                                  (ITE #doWork
                                     #incRevokeAddr
                                     #revokeAddr);
          LetE newEpoch <- Add [#revokerEpoch; ITE (Or [Eq #incRevokeAddr #revokerEnd; #workStart]) $1 $0];

          @RetE _ RevokerUpdState (STRUCT { "tags" ::= #newTags;
                                            "revokerEpoch" ::= #newEpoch;
                                            "revokerKick" ::= Const ty Bool false;
                                            "revokeAddr" ::= #newRevokeAddr })
        ).
    End LetExpr.

    Definition revoker: Action ty (getModLists specDecl) (Bit 0) :=
      ( RegRead mem <- "mem" in specLists;
        RegRead tags <- "tags" in specLists;
        RegRead revokerEpoch <- "revokerEpoch" in specLists;
        RegRead revokerKick <- "revokerKick" in specLists;
        RegRead revokerStart <- "revokerStart" in specLists;
        RegRead revokerEnd <- "revokerEnd" in specLists;
        RegRead revokeAddr <- "revokeAddr" in specLists;

        Let revokerUpdState: RevokerUpdState <- STRUCT { "tags" ::= #tags;
                                                         "revokerEpoch" ::= #revokerEpoch;
                                                         "revokerKick" ::= #revokerKick;
                                                         "revokeAddr" ::= #revokeAddr };

        LetL newRevokerUpdState <- revokerExpr mem revokerStart revokerEnd revokerUpdState;

        RegWrite "tags" in specLists <- #newRevokerUpdState`"tags";
        RegWrite "revokerEpoch" in specLists <- ##newRevokerUpdState`"revokerEpoch";
        RegWrite "revokerKick" in specLists <- ##newRevokerUpdState`"revokerKick";
        RegWrite "revokeAddr" in specLists <- ##newRevokerUpdState`"revokeAddr";
        Retv ).
  End Ty.

  Definition spec: Mod := {|modDecl := specDecl;
                            modActions := fun ty => [step ty; interrupts ty; revoker ty]|}.

  Definition RegsInvariant: FuncState (mregs specLists) -> Prop.
  Admitted.

  Definition SpecInvariant (s: ModStateModDecl specDecl) : Prop :=
    RegsInvariant (stateRegs s) /\
      (stateMems s = tt) /\
      (stateRegUs s = tt) /\
      (stateMemUs s = tt).

  Theorem specInvariantPreserved: forall old new puts gets,
      SpecInvariant old ->
      SemAction (step type) old new puts gets Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Theorem interruptsInvariantPreserved: forall old new puts gets,
      SpecInvariant old ->
      SemAction (interrupts type) old new puts gets Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Theorem revokerInvariantPreserved: forall old new puts gets,
      SpecInvariant old ->
      SemAction (revoker type) old new puts gets Zmod.zero ->
      SpecInvariant new.
  Admitted.

  Ltac simplifyAluExpr v :=
    let x := eval cbn delta -[evalFromBitStruct] beta iota in v in
      let x := eval cbv delta [mapSameTuple updSameTuple updSameTupleNat Bool.transparent_Is_true]
                 beta iota in x in
        let x := eval cbn delta -[evalFromBitStruct] beta iota in x in
          x.

  (*
  Definition evalStepExpr (state: Expr type AllSpecState): type AllSpecState :=
    ltac:(let x := simplifyAluExpr (evalLetExpr (stepExpr state)) in exact x).
   *)
End Spec.
