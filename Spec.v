From Stdlib Require Import String List ZArith Zmod Bool.
Require Import Guru.Syntax Guru.Notations Guru.Semantics Guru.Library.
Require Import Cheriot.Alu Cheriot.Switcher.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Spec.
  Variable MemWidth: nat.
  Variable MemWidthGe3: MemWidth >= 3.
  Definition MemByteSz := Nat.pow 2 MemWidth.
  Definition Mem64Sz := Nat.pow 2 (MemWidth - 3).
  Definition switcherLength := Eval compute in (length switcher).
  Definition specInst: type (Array switcherLength (Bit 8)) := Build_SameTuple (tupleElems := switcher)
                                                                (I: Is_true (length switcher =? switcherLength)).
  Variable specMemR: type (Array MemByteSz (Bit 8)).
  Variable specTagsR: type (Array Mem64Sz Bool).
  Variable specRegsR: type (Array NumRegs FullECapWithTag).
  Definition specWaits := Default (Array NumRegs Bool).
  Variable specCsrsR: type Csrs.
  Variable specScrsR: type Scrs.
  Variable specInterruptsR: type Interrupts.

  Variable RevStart: Z.
  Variable RevByteSz: Z.
  Variable RevEachBitLgNumBytes: Z.
  Variable RevEachBitLgNumBytesInMem: (RevEachBitLgNumBytes < Z.of_nat MemWidth)%Z.
  Variable RevInMem: (RevStart + RevByteSz < Z.of_nat MemByteSz)%Z.
  Variable HeapStart: Z.
  Definition HeapEnd := (HeapStart + (RevByteSz * (Z.shiftl 1 RevEachBitLgNumBytes) * 8))%Z.
  Variable HeapInMem: (HeapEnd < Z.of_nat MemByteSz)%Z.

  Definition RevStartAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ RevStart.
  Definition HeapStartAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ HeapStart.
  Definition HeapEndAddr: type (Bit (AddrSz + 1)) := bits.of_Z _ HeapEnd.

  Local Open Scope string_scope.
  Local Open Scope guru_scope.

  Definition SpecState := STRUCT_TYPE {
                              "specMem" :: Array MemByteSz (Bit 8) ;
                              "specTags" :: Array Mem64Sz Bool ;
                              "specRegs" :: Array NumRegs FullECapWithTag ;
                              "specCsrs" :: Csrs ;
                              "specScrs" :: Scrs }.

  Definition AllSpecState := STRUCT_TYPE {
                                 "specState" :: SpecState;
                                 "specInterrupts" :: Interrupts }.

  Definition specInit: type SpecState := STRUCT_CONST {
                                             "specMem" ::= specMemR;
                                             "specTags" ::= specTagsR;
                                             "specRegs" ::= specRegsR;
                                             "specCsrs" ::= specCsrsR;
                                             "specScrs" ::= specScrsR }.

  Definition specRegs := [("specState", Build_Reg _ specInit);
                          ("specInterrupts", Build_Reg _ specInterruptsR)].

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

    Definition isInHeap (addr: ty (Bit (AddrSz + 1))): Expr ty Bool :=
      And [Sge #addr (ConstBit HeapStartAddr); Slt #addr (ConstBit HeapEndAddr)].

    Definition revBitNum (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit (AddrSz + 1)) :=
      Srl (Sub #addr (ConstBit HeapStartAddr)) (ConstBit (bits.of_Z (Z.of_nat MemWidth) RevEachBitLgNumBytes)).

    Definition revBitByteAddr (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit (AddrSz + 1)) :=
      Srl (revBitNum addr) (ConstBit (bits.of_Z 2 3)).

    Definition revBitByteOffset (addr: ty (Bit (AddrSz + 1))): Expr ty (Bit 3) :=
      TruncLsb ((AddrSz + 1) - 3) 3 (revBitNum addr).

    Section LetExpr.
      Variable state: ty AllSpecState.

      Ltac specSimpl x :=
        (let y := eval cbv [getFinStruct structList arraySize fieldK forceOption getFinStructOption length
                              fst snd String.eqb Ascii.eqb Bool.eqb fieldNameK nth_pf finNum] in x in
           simplKind y).

      Notation specSimpl x := ltac:(specSimpl x) (only parsing).

      Definition stepExpr: LetExpr ty AllSpecState := specSimpl
        ( LetE specInst : Array switcherLength (Bit 8) <- Const ty _ specInst;
          LetE specMem <- ##state`"specState"`"specMem";
          LetE specTags <- ##state`"specState"`"specTags";
          LetE specRegs <- ##state`"specState"`"specRegs";
          LetE specCsrs <- ##state`"specState"`"specCsrs";
          LetE specScrs <- ##state`"specState"`"specScrs";
          LetE specInterrupts <- ##state`"specInterrupts";
          LetE pcc : FullECapWithTag <- #specRegs $[ 0 ];
          LetE pcVal : Addr <- #pcc`"addr";
          LetE BoundsException : Bool <- And [Slt (ZeroExtend 1 #pcVal) (##pcc`"ecap"`"top")];
          LetE pcAluOut: PcAluOut <- STRUCT { "pcVal" ::= #pcVal;
                                              "BoundsException" ::= #BoundsException };
          LetE inst: Inst <- ToBit (slice #specInst #pcVal (Z.to_nat InstSz/8));
          LETE decodeOut: DecodeOut <- decode inst;
          
          LetE aluIn: AluIn <- STRUCT { "pcAluOut" ::= #pcAluOut;
                                        "decodeOut" ::= #decodeOut;
                                        "regs" ::= #specRegs;
                                        "waits" ::= Const ty _ specWaits;
                                        "csrs" ::= #specCsrs;
                                        "scrs" ::= #specScrs;
                                        "interrupts" ::= #specInterrupts };
          LetE pcTag <- #pcc`"tag";
          LetE pcCap <- #pcc`"ecap";
          LETE aluOut: AluOut <- alu pcTag pcCap aluIn;
          LetE memAddr: Addr <- ##aluOut`"multicycleOp"`"memAddr";
          LetE memSz: Bit MemSz <- Sll $1 (##aluOut`"multicycleOp"`"memSz");
          LetE isCap: Bool <- isZero #memSz;
          LetE ldUn: Bool <- ##aluOut`"multicycleOp"`"LoadUnsigned";

          LetE bytes: Array _ (Bit 8) <- slice #specMem #memAddr (Z.to_nat DXlenBytes);
          LetE fullCap <- FromBit FullCap (ToBit #bytes);
          LetE ldCap: Cap <- #fullCap`"cap";
          LetE ldVal <- FromBit (Array (Z.to_nat XlenBytes) (Bit 8)) #fullCap`"addr";
          LetE ldValFinal <- ToBit (ITE #ldUn (ArrayZeroExtend #memSz #ldVal) (ArraySignExtend #memSz #ldVal));
          LETE ldECap: ECap <- decodeCap ldCap ldValFinal;
          LetE ldECapFinal: ECap <- ITE #isCap #ldECap ConstDef;
          LetE memTagAddr: Bit (AddrSz - MemSz) <- TruncMsb _ MemSz #memAddr;
          LetE ldTag: Bool <- #specTags@[#memTagAddr];
          LetE ldBase: Bit (AddrSz + 1) <- #ldECap`"base";
          LetE revByte: Array 8 Bool <- FromBit (Array 8 Bool) #specMem@[revBitByteAddr ldBase];
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

          LETE stCap: Cap <- encodeCap stECap;
          LetE stBits: Bit DXlen <- {< ToBit #stCap, ##aluOut`"multicycleOp"`"storeVal"`"addr" >};
          LetE stBytes: Array (Z.to_nat DXlenBytes) (Bit 8) <- FromBit _ #stBits;
          LetE Store: Bool <- ##aluOut`"multicycleOp"`"Store";

          LETE updMem <- updSlice #specMem #memAddr #stBytes #memSz;

          LetE newMem <- ITE #Store #updMem #specMem;
          LetE newTags: Array Mem64Sz Bool <- #specTags
                                                @[#memTagAddr <- ITE (And [#isCap; #Store])
                                                                   (##aluOut`"multicycleOp"`"storeVal"`"tag")
                                                                   #ldTag];

          LetE newSpecState: SpecState <- STRUCT { "specMem" ::= #newMem;
                                                   "specTags" ::= #newTags;
                                                   "specRegs" ::= #newRegs;
                                                   "specCsrs" ::= #aluOut`"csrs";
                                                   "specScrs" ::= ##aluOut`"scrs" };
          @RetE _ AllSpecState (STRUCT { "specState" ::= #newSpecState;
                                         "specInterrupts" ::= ##aluOut`"interrupts" })).
    End LetExpr.

    Definition step: Action ty (getModLists specDecl) (Bit 0) :=
      ( RegRead specState <- "specState" in specLists;
        RegRead specInterrupts <- "specInterrupts" in specLists;
        Let fullState <- STRUCT { "specState" ::= #specState;
                                  "specInterrupts" ::= #specInterrupts };
        LetL updRegs : AllSpecState <- stepExpr fullState;
        Put "pcOut" in specLists <- ##specState`"specRegs" $[0]`"addr";
        RegWrite "specState" in specLists <- #updRegs`"specState";
        RegWrite "specInterrupts" in specLists <- ##updRegs`"specInterrupts";
        Return ConstDef).

    Definition async: Action ty (getModLists specDecl) (Bit 0) :=
      ( Get interrupts <- "interrupts" in specLists;
        RegRead specInterrupts <- "specInterrupts" in specLists;
        RegWrite "specInterrupts" in specLists <- Or [#interrupts; #specInterrupts];
        Return ConstDef ).
  End Ty.

  Definition spec: Mod := {|modDecl := specDecl;
                            modActions := fun ty => [step ty; async ty]|}.

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

  Theorem asyncInvariantPreserved: forall old new puts gets,
      SpecInvariant old ->
      SemAction (async type) old new puts gets Zmod.zero ->
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
