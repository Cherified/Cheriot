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

    Definition signOrZeroExtend (unsigned: Expr ty Bool) n (v: Expr ty (Bit n)) :=
      ITE unsigned (ZeroExtendTo Xlen v) (SignExtendTo Xlen v).

    Section LetExpr.
      Variable state: Expr ty AllSpecState.

      Ltac specSimpl x :=
        (let y := eval cbv [getFinStruct structList arraySize fieldK forceOption getFinStructOption length
                              fst snd String.eqb Ascii.eqb Bool.eqb fieldNameK nth_pf finNum] in x in
           simplKind y).

      Notation specSimpl x := ltac:(specSimpl x) (only parsing).

      Definition stepExpr: LetExpr ty AllSpecState := specSimpl
        ( LetE specInst : Array switcherLength (Bit 8) <- Const ty _ specInst;
          LetE specMem <- state`"specState"`"specMem";
          LetE specTags <- state`"specState"`"specTags";
          LetE specRegs <- state`"specState"`"specRegs";
          LetE specCsrs <- state`"specState"`"specCsrs";
          LetE specScrs <- state`"specState"`"specScrs";
          LetE specInterrupts <- state`"specInterrupts";
          LetE pcc : FullECapWithTag <- #specRegs $[ 0 ];
          LetE pcVal : Addr <- #pcc`"addr";
          LetE BoundsException : Bool <- And [Slt (ZeroExtend 1 #pcVal) (##pcc`"ecap"`"top")];
          LetE pcAluOut: PcAluOut <- STRUCT { "pcVal" ::= #pcVal;
                                              "BoundsException" ::= #BoundsException };
          LetE inst: Inst <- {< #specInst@[Add [#pcVal; $3]],
                         #specInst@[Add [#pcVal; $2]],
                         #specInst@[Add [#pcVal; $1]],
                         #specInst@[#pcVal] >};
          LETE decodeOut: DecodeOut <- decode #inst;
          
          LetE aluIn: AluIn <- STRUCT { "pcAluOut" ::= #pcAluOut;
                                        "decodeOut" ::= #decodeOut;
                                        "regs" ::= #specRegs;
                                        "waits" ::= Const ty _ specWaits;
                                        "csrs" ::= #specCsrs;
                                        "scrs" ::= #specScrs;
                                        "interrupts" ::= #specInterrupts };
          LETE aluOut: AluOut <- alu (#pcc`"tag") (##pcc`"ecap") #aluIn;
          LetE memAddr: Addr <- #aluOut`"memAddr";
          LetE memSz: Bit MemSzSz <- #aluOut`"memSz";
          LetE ldUn: Bool <- #aluOut`"LoadUnsigned";

          LetE byte7: Bit 8 <- #specMem@[Add [#memAddr; $7]];
          LetE byte6: Bit 8 <- #specMem@[Add [#memAddr; $6]];
          LetE byte5: Bit 8 <- #specMem@[Add [#memAddr; $5]];
          LetE byte4: Bit 8 <- #specMem@[Add [#memAddr; $4]];
          LetE byte3: Bit 8 <- #specMem@[Add [#memAddr; $3]];
          LetE byte2: Bit 8 <- #specMem@[Add [#memAddr; $2]];
          LetE byte1: Bit 8 <- #specMem@[Add [#memAddr; $1]];
          LetE byte0: Bit 8 <- #specMem@[#memAddr];
          LetE ldNoCap: Bit 32 <- {< #byte7, #byte6, #byte5, #byte4 >};
          LetE ldCap: Cap <- FromBit Cap #ldNoCap;
          LetE ldValFinal: Data <-
                             ITE (Eq #memSz $0)
                             (signOrZeroExtend #ldUn #byte0)
                             (ITE (Eq #memSz $1)
                                (signOrZeroExtend #ldUn {<#byte1, #byte0>})
                                {<#byte3, #byte2, #byte1, #byte0>});
          
          LETE ldECap: ECap <- decodeCap #ldCap #ldValFinal;
          LetE ldECapFinal: ECap <- ITE (Eq #memSz $3) #ldECap ConstDef;
          LetE memTagAddr: Bit (AddrSz - 3) <- TruncMsb (AddrSz - 3) 3 #memAddr;
          LetE ldTag: Bool <- #specTags@[#memTagAddr];
          LetE ldTagFinal: Bool <- ITE (Eq #memSz $3) #ldTag (ConstBool false);

          LetE ldFinal: FullECapWithTag <- STRUCT { "tag" ::= #ldTagFinal;
                                                    "ecap" ::= #ldECapFinal;
                                                    "addr" ::= #ldValFinal };

          LetE ldRegIdx <- #aluOut`"ldRegIdx";
          LetE aluOutRegs: Array NumRegs FullECapWithTag <- #aluOut`"regs";
          LetE newRegs: Array NumRegs FullECapWithTag <- #aluOutRegs
                          @[ #ldRegIdx <-  ITE (#aluOut`"Load") #ldFinal
                               (#aluOutRegs@[#ldRegIdx])];

          LETE stCap: Cap <- encodeCap (##aluOut`"storeVal"`"ecap");
          LetE stBits: Bit DXlen <- {< ToBit #stCap, ##aluOut`"storeVal"`"addr" >};
          LetE Store: Bool <- #aluOut`"Store";

          LetE newMem: Array MemByteSz (Bit 8) <- #specMem
                         @[Add [#memAddr; $7] <- ITE (And [Eq #memSz $3; #Store]) #stBits`[63:56] #byte7]
                         @[Add [#memAddr; $6] <- ITE (And [Eq #memSz $3; #Store]) #stBits`[55:48] #byte6]
                         @[Add [#memAddr; $5] <- ITE (And [Eq #memSz $3; #Store]) #stBits`[47:40] #byte5]
                         @[Add [#memAddr; $4] <- ITE (And [Eq #memSz $3; #Store]) #stBits`[39:32] #byte4]
                         @[Add [#memAddr; $3] <- ITE (And [Sge #memSz $2; #Store]) #stBits`[31:24] #byte3]
                         @[Add [#memAddr; $2] <- ITE (And [Sge #memSz $2; #Store]) #stBits`[23:16] #byte2]
                         @[Add [#memAddr; $1] <- ITE (And [Sge #memSz $1; #Store]) #stBits`[15:8] #byte1]
                         @[#memAddr <- ITE #Store #stBits`[7:0] #byte0];

          LetE newTags: Array Mem64Sz Bool <- #specTags
                          @[#memTagAddr <- ITE (And [Eq #memSz $3; #Store]) (##aluOut`"storeVal"`"tag") #ldTag];

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
        LetL updRegs : AllSpecState <- stepExpr (STRUCT { "specState" ::= #specState;
                                                        "specInterrupts" ::= #specInterrupts });
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

  Definition evalStepExpr (state: Expr type AllSpecState): type AllSpecState :=
    ltac:(let x := simplifyAluExpr (evalLetExpr (stepExpr state)) in exact x).

End Spec.
