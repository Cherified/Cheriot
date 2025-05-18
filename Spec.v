Require Import String List.
Require Import Guru.Lib.Library Guru.Lib.Word.
Require Import Guru.Syntax Guru.Notations Guru.Semantics.
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
  Variable specTagsR: type (Array Mem64Sz Bool).
  Variable specMemR: type (Array MemByteSz (Bit 8)).
  Variable specRegsR: type (Array NumRegs FullECapWithTag).
  Definition specWaits := Default (Array NumRegs Bool).
  Variable specCsrsR: type Csrs.
  Variable specScrsR: type Scrs.
  Variable specInterruptsR: type Interrupts.

  Variable mtccVal: type Addr.
  Variable switcherMatches: ReadArrayFromListZEq specMemR (wordToNat mtccVal) switcher.

  Local Open Scope string_scope.
  Definition specAllRegs := [("specMem", Build_Reg _ specMemR);
                             ("specTags", Build_Reg _ specTagsR);
                             ("specRegs", Build_Reg _ specRegsR);
                             ("specCsrs", Build_Reg _ specCsrsR);
                             ("specScrs", Build_Reg _ specScrsR);
                             ("specInterrupts", Build_Reg _ specInterruptsR)].

  Definition specDecl: ModDecl := {|modRegs := specAllRegs;
                                    modMems := nil;
                                    modRegUs := nil;
                                    modMemUs := nil;
                                    modSends := [("pcOut", Addr)];
                                    modRecvs := [("interrupts", Interrupts)]|}.
  Local Close Scope string_scope.

  Definition specLists := getModLists specDecl.

  Section Ty.
    Variable ty: Kind -> Type.
    Local Open Scope guru_scope.

    Definition signOrZeroExtend (unsigned: Expr ty Bool) n (v: Expr ty (Bit n)) :=
      ITE unsigned (ZeroExtendTo Xlen v) (SignExtendTo Xlen v).

    Definition step: Action ty (getModLists specDecl) (Bit 0) :=
      ( RegRead specMem <- "specMem" in specLists;
        RegRead specTags <- "specTags" in specLists;
        RegRead specRegs <- "specRegs" in specLists;
        RegRead specCsrs <- "specCsrs" in specLists;
        RegRead specScrs <- "specScrs" in specLists;
        RegRead specInterrupts <- "specInterrupts" in specLists;
        Let pcc : FullECapWithTag <- #specRegs $[ 0 ];
        Let pcVal : Addr <- #pcc`"addr";
        Put "pcOut" in specLists <- #pcVal;
        Let BoundsException : Bool <- And [Slt (ZeroExtend 1 #pcVal) (#pcc`"ecap"`"top")];
        Let pcAluOut: PcAluOut <- STRUCT { "pcVal" ::= #pcVal;
                                           "BoundsException" ::= #BoundsException };
        Let inst: Inst <- {< #specMem@[Add [#pcVal; $3]],
                      #specMem@[Add [#pcVal; $2]],
                      #specMem@[Add [#pcVal; $1]],
                      #specMem@[#pcVal] >};
        LetL decodeOut: DecodeOut <- decode #inst;
  
        Let aluIn: AluIn <- STRUCT { "pcAluOut" ::= #pcAluOut;
                                     "decodeOut" ::= #decodeOut;
                                     "regs" ::= #specRegs;
                                     "waits" ::= Const ty _ specWaits;
                                     "csrs" ::= #specCsrs;
                                     "scrs" ::= #specScrs;
                                     "interrupts" ::= #specInterrupts };
        LetL aluOut: AluOut <- alu (#pcc`"tag") (#pcc`"ecap") #aluIn;
        Let memAddr: Addr <- #aluOut`"memAddr";
        Let memSz: Bit MemSzSz <- #aluOut`"memSz";
        Let ldUn: Bool <- #aluOut`"LoadUnsigned";
  
        Let ldCap: Cap <- FromBit Cap {< #specMem@[Add [#memAddr; $7]],
                       #specMem@[Add [#memAddr; $6]],
                       #specMem@[Add [#memAddr; $5]],
                       #specMem@[Add [#memAddr; $4]] >};
        Let ldValFinal: Data <-
                          ITE (Eq #memSz $0)
                          (signOrZeroExtend #ldUn #specMem@[#memAddr])
                          (ITE (Eq #memSz $1)
                             (signOrZeroExtend #ldUn {<#specMem@[Add [#memAddr; $1]], #specMem@[#memAddr]>})
                             {< #specMem@[Add [#memAddr; $3]],
                               #specMem@[Add [#memAddr; $2]],
                               #specMem@[Add [#memAddr; $1]],
                               #specMem@[#memAddr] >});
        LetL ldECap: ECap <- decodeCap #ldCap #ldValFinal;
        Let ldECapFinal: ECap <- ITE (Eq #memSz $3) #ldECap ConstDef;
        Let memTagAddr: Bit (AddrSz - 3) <- TruncMsb (AddrSz - 3) 3 #memAddr;
        Let ldTag: Bool <- #specTags@[#memTagAddr];
        Let ldTagFinal: Bool <- ITE (Eq #memSz $3) #ldTag (ConstBool false);

        Let ldFinal: FullECapWithTag <- STRUCT { "tag" ::= #ldTagFinal;
                                                 "ecap" ::= #ldECapFinal;
                                                 "addr" ::= #ldValFinal };

        Let ldRegIdx <- #aluOut`"ldRegIdx";
        Let aluOutRegs: Array NumRegs FullECapWithTag <- #aluOut`"regs";
        Let newRegs: Array NumRegs FullECapWithTag <- #aluOutRegs
                       @[ #ldRegIdx <-  ITE (##aluOut`"Load") #ldFinal
                            (#aluOutRegs@[#ldRegIdx])];

        LetL stCap: Cap <- encodeCap (##aluOut`"storeVal"`"ecap");
        Let stCapBits: Bit DXlen <- {< ToBit #stCap, ##aluOut`"storeVal"`"addr" >};
        Let stCapArr: Array 8 (Bit 8) <- FromBit (Array 8 (Bit 8)) #stCapBits;
        Let Store: Bool <- #aluOut`"Store";

        Let newMem: Array MemByteSz (Bit 8) <- #specMem
                      @[Add [#memAddr; $7] <- ITE (And [Eq #memSz $3; #Store]) #stCapArr$[7]
                          (#specMem@[Add [#memAddr; $7]])]
                      @[Add [#memAddr; $6] <- ITE (And [Eq #memSz $3; #Store]) #stCapArr$[6]
                          (#specMem@[Add [#memAddr; $6]])]
                      @[Add [#memAddr; $5] <- ITE (And [Eq #memSz $3; #Store]) #stCapArr$[5]
                          (#specMem@[Add [#memAddr; $5]])]
                      @[Add [#memAddr; $4] <- ITE (And [Eq #memSz $3; #Store]) #stCapArr$[4]
                          (#specMem@[Add [#memAddr; $4]])]
                      @[Add [#memAddr; $3] <- ITE (And [Sge #memSz $2; #Store]) #stCapArr$[3]
                          (#specMem@[Add [#memAddr; $3]])]
                      @[Add [#memAddr; $2] <- ITE (And [Sge #memSz $2; #Store]) #stCapArr$[2]
                          (#specMem@[Add [#memAddr; $2]])]
                      @[Add [#memAddr; $1] <- ITE (And [Sge #memSz $1; #Store]) #stCapArr$[1]
                          (#specMem@[Add [#memAddr; $1]])]
                      @[#memAddr <- ITE #Store #stCapArr$[0] (#specMem@[#memAddr])];

        Let newTags: Array Mem64Sz Bool <- #specTags
                           @[#memTagAddr <- ITE (And [Eq #memSz $3; #Store]) (##aluOut`"storeVal"`"tag") #ldTag];

        RegWrite "specMem" in specLists <- #newMem;
        RegWrite "specTags" in specLists <- #newTags;
        RegWrite "specRegs" in specLists <- #newRegs;
        RegWrite "specCsrs" in specLists <- #aluOut`"csrs";
        RegWrite "specScrs" in specLists <- ##aluOut`"scrs";
        RegWrite "specInterrupts" in specLists <- ##aluOut`"interrupts";
        Return ConstDef ).

    Definition asyncInterrupts: Action ty (getModLists specDecl) (Bit 0) :=
      ( Get interrupts <- "interrupts" in specLists;
        RegRead specInterrupts <- "specInterrupts" in specLists;
        RegWrite "specInterrupts" in specLists <- Or [#interrupts; #specInterrupts];
        Return ConstDef ).
  End Ty.

  Definition spec: Mod := {|modDecl := specDecl;
                            modActions := fun ty => [step ty; asyncInterrupts ty]|}.

  Definition SpecInvariant: ModStateModDecl specDecl -> Prop.
  Admitted.

  Theorem specInvariantPreserved: forall old new puts gets,
      SpecInvariant old ->
      SemAction (step type) old new puts gets WO ->
      SpecInvariant new.
  Admitted.
End Spec.
