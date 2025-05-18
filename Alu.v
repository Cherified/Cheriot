Require Import String List PeanoNat.
Require Import Guru.Lib.Word Guru.Lib.Library.
Require Import Guru.Syntax Guru.Notations.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Definition Xlen := 32.
Definition Data := Eval compute in Bit Xlen.
Definition AddrSz := Eval compute in Xlen.
Definition Addr := Eval compute in Bit AddrSz.
Definition LgAddrSz := Eval compute in Nat.log2_up AddrSz.
Definition ExpSz := Eval compute in LgAddrSz.
Definition CapExceptSz := 5.

Definition InstSz := 32.
Definition Inst := Bit 32.
Definition CompInstSz := 16.
Definition CompInst := Bit 16.
Definition HasComp := true.
Definition NumLsb0BitsInstAddr := Eval compute in (Nat.log2_up ((if HasComp then CompInstSz else InstSz)/8)).

Definition RegIdSz := 4.
Definition NumRegs := Eval compute in (Nat.pow 2 RegIdSz).
Definition RegFixedIdSz := 5.
Definition NumRegsFixed := Eval compute in (Nat.pow 2 RegFixedIdSz).

Definition Imm12Sz := 12.
Definition Imm20Sz := 20.
Definition DecImmSz := Eval compute in (S Imm20Sz).

Definition CapPermSz := 6.
Definition CapOTypeSz := 3.
Definition CapcMSz := 8.
Definition CapBSz := Eval compute in CapcMSz + 1.
Definition CapMSz := Eval compute in CapBSz.

Definition IeBit := 4. (* 4th bit counting from 0, i.e. mstatus[3] = IE *)

Section Exceptions.
  Definition BoundsViolation := 1.
  Definition TagViolation := 2.
  Definition SealViolation := 3.
  Definition ExViolation := 17.
  Definition LdViolation := 18.
  Definition SdViolation := 19.
  (* Note: Absent Definition McLdViolation := 20. Clear loaded tag when Mc is absent *)
  Definition McSdViolation := 21.
  Definition SrViolation := 24.
  Definition IllegalException := 2.
  Definition EBreakException := 3.
  Definition LdAlignException := 4.
  Definition SdAlignException := 6.
  Definition ECallException := 11.
  Definition CapException := 28.

  Definition McauseSz := 5.
End Exceptions.

Section Interrupts.
  Definition Mei := 11.
  Definition Mti := 7.
End Interrupts.

Section Csr.
  (* TODO CSRs performance counters *)
  Definition Mcycle := hex "B00".
  Definition Mtime := hex "B01".
  Definition Minstret := hex "B02".
  Definition Mcycleh := hex "B80".
  Definition Mtimeh := hex "B81".
  Definition Minstreth := hex "B82".
  Definition Mshwm := hex "BC1".
  Definition Mshwmb := hex "BC2".

  Definition Mstatus := hex "300".
  Definition Mcause := hex "342".
  Definition Mtval := hex "343".

  Definition MshwmAlign := 4.
  Definition CsrIdSz := Imm12Sz.
  Definition CsrId := Bit CsrIdSz.
End Csr.

Section Scr.
  Definition Mtcc := 28.
  Definition Mtdc := 29.
  Definition Mscratchc := 30.
  Definition Mepcc := 31.
End Scr.

Local Open Scope guru_scope.

Definition Cap : Kind := STRUCT_TYPE {
                             "R" :: Bool;
                             "p" :: Array CapPermSz Bool;
                             "oType" :: Bit CapOTypeSz;
                             "cE" :: Bit ExpSz;
                             "cM" :: Bit CapcMSz;
                             "B" :: Bit CapBSz }.

Definition CapPerms := STRUCT_TYPE { "U0" :: Bool ;
                                     "SE" :: Bool ;
                                     "US" :: Bool ;
                                     "EX" :: Bool ;
                                     "SR" :: Bool ;
                                     "MC" :: Bool ;
                                     "LD" :: Bool ;
                                     "SL" :: Bool ;
                                     "LM" :: Bool ;
                                     "SD" :: Bool ;
                                     "LG" :: Bool ;
                                     "GL" :: Bool }.

Definition ECap := STRUCT_TYPE { "R"     :: Bool;
                                 "perms" :: CapPerms;
                                 "oType" :: Bit CapOTypeSz;
                                 "E"     :: Bit ExpSz;
                                 "top"   :: Bit (AddrSz + 1);
                                 "base"  :: Bit (AddrSz + 1) }.

Definition FullECapWithTag := STRUCT_TYPE { "tag" :: Bool;
                                            "ecap" :: ECap;
                                            "addr" :: Addr }.

Definition DXlen := Eval compute in Xlen + Xlen.
Definition MemSzSz := Eval compute in Nat.log2_up (Nat.log2_up (DXlen/8)).
Definition FullCapSz := Eval compute in Xlen + size Cap.
Definition NumBytesFullCapSz := Eval compute in (FullCapSz/8).
Definition LgNumBytesFullCapSz := Eval compute in lgCeil NumBytesFullCapSz.

Section Fields.
  Context {ty: Kind -> Type}.
  Variable inst: Expr ty (Bit InstSz).

  Definition instSizeField := (0, 2).
  Definition opcodeField := (2, 5).
  Definition funct3Field := (12, 3).
  Definition funct7Field := (25, 7).
  Definition funct6Field := (26, 6).
  Definition immField := (20, Imm12Sz).
  Definition rs1Field := (15, RegIdSz).
  Definition rs2Field := (20, RegIdSz).
  Definition rdField := (7, RegIdSz).
  Definition rs1FixedField := (15, RegFixedIdSz).
  Definition rs2FixedField := (20, RegFixedIdSz).
  Definition rdFixedField := (7, RegFixedIdSz).
  Definition auiLuiField := (12, Imm20Sz).

  Notation extractFieldFromInst span := (ConstExtract (InstSz - (snd span) - (fst span)) (snd span) (fst span) inst).

  Definition instSize := extractFieldFromInst instSizeField.
  Definition opcode := extractFieldFromInst opcodeField.
  Definition funct3 := extractFieldFromInst funct3Field.
  Definition funct7 := extractFieldFromInst funct7Field.
  Definition funct6 := extractFieldFromInst funct6Field.
  Definition rs1 := extractFieldFromInst rs1Field.
  Definition rs2 := extractFieldFromInst rs2Field.
  Definition rd := extractFieldFromInst rdField.
  Definition rs1Fixed := extractFieldFromInst rs1FixedField.
  Definition rs2Fixed := extractFieldFromInst rs2FixedField.
  Definition rdFixed := extractFieldFromInst rdFixedField.
  Definition c0 := 0.
  Definition ra := 1.
  Definition sp := 2.

  Definition imm := extractFieldFromInst immField.
  Definition branchOffset := ({< extractFieldFromInst (31, 1),
                                 extractFieldFromInst ( 7, 1),
                                 extractFieldFromInst (25, 6),
                                 extractFieldFromInst ( 8, 4), ConstBit WO~0 >}).
  Definition jalOffset := ({< extractFieldFromInst (31,  1),
                              extractFieldFromInst (12,  8),
                              extractFieldFromInst (20,  1),
                              extractFieldFromInst (21, 10), ConstBit WO~0 >}).
  Definition auiLuiOffset := extractFieldFromInst auiLuiField.

  Definition isCompressed := isAllOnes (TruncLsb (InstSz - 2) 2 inst).
End Fields.

Section Cap.
  Variable ty: Kind -> Type.

  Section CapPerms.
    Definition decodePerms (rawPerms: Expr ty (Array CapPermSz Bool)) : LetExpr ty CapPerms :=
      ( LetE initPerms : CapPerms <- (ConstTDefK CapPerms) `{ "GL" <- rawPerms $[5] };
        RetE (ITE (rawPerms $[4])
                (ITE (rawPerms $[3])
                   (##initPerms
                      `{ "MC" <- ConstBool true }
                      `{ "LD" <- ConstBool true }
                      `{ "SL" <- rawPerms $[2] }
                      `{ "LM" <- rawPerms $[1] }
                      `{ "SD" <- ConstBool true }
                      `{ "LG" <- rawPerms $[0] })
                   (ITE (rawPerms $[2])
                      (##initPerms
                         `{ "MC" <- ConstBool true }
                         `{ "LD" <- ConstBool true }
                         `{ "LM" <- rawPerms $[1] }
                         `{ "LG" <- rawPerms $[0] })
                      (ITE (Not (Or [rawPerms $[1]; rawPerms $[0]]))
                         (##initPerms
                            `{ "MC" <- ConstBool true }
                            `{ "SD" <- ConstBool true })
                         (##initPerms
                            `{ "LD" <- rawPerms $[1] }
                            `{ "SD" <- rawPerms $[0] }))))
                (ITE (rawPerms $[3])
                   (##initPerms
                      `{ "EX" <- ConstBool true }
                      `{ "SR" <- rawPerms $[2] }
                      `{ "MC" <- ConstBool true }
                      `{ "LD" <- ConstBool true }
                      `{ "LM" <- rawPerms $[1] }
                      `{ "LG" <- rawPerms $[0] })
                   (##initPerms
                      `{ "U0" <- rawPerms $[2] }
                      `{ "SE" <- rawPerms $[1] }
                      `{ "US" <- rawPerms $[0] })))).

    Definition fixPerms (perms: Expr ty CapPerms) : Expr ty CapPerms :=
      (ITE (And [perms`"EX"; perms`"LD"; perms`"MC"])
         (perms
            `{ "U0" <- ConstBool false }
            `{ "SE" <- ConstBool false }
            `{ "US" <- ConstBool false }
            `{ "SL" <- ConstBool false }
            `{ "SD" <- ConstBool false })
         (ITE (And [perms`"LD"; perms`"MC"; perms`"SD"])
            (perms
               `{ "U0" <- ConstBool false }
               `{ "SE" <- ConstBool false }
               `{ "US" <- ConstBool false }
               `{ "EX" <- ConstBool false }
               `{ "SR" <- ConstBool false })
            (ITE (And [perms`"LD"; perms`"MC"])
               (perms
                  `{ "U0" <- ConstBool false }
                  `{ "SE" <- ConstBool false }
                  `{ "US" <- ConstBool false }
                  `{ "EX" <- ConstBool false }
                  `{ "SR" <- ConstBool false }
                  `{ "SL" <- ConstBool false }
                  `{ "SD" <- ConstBool false })
               (ITE (And [perms`"SD"; perms`"MC"])
                  (perms
                     `{ "U0" <- ConstBool false }
                     `{ "SE" <- ConstBool false }
                     `{ "US" <- ConstBool false }
                     `{ "EX" <- ConstBool false }
                     `{ "SR" <- ConstBool false }
                     `{ "LD" <- ConstBool false }
                     `{ "SL" <- ConstBool false }
                     `{ "LM" <- ConstBool false }
                     `{ "LG" <- ConstBool false })
                  (ITE (Or [perms`"LD"; perms`"SD"])
                     (perms
                     `{ "U0" <- ConstBool false }
                     `{ "SE" <- ConstBool false }
                     `{ "US" <- ConstBool false }
                     `{ "EX" <- ConstBool false }
                     `{ "SR" <- ConstBool false }
                     `{ "MC" <- ConstBool false }
                     `{ "SL" <- ConstBool false }
                     `{ "LM" <- ConstBool false }
                     `{ "LG" <- ConstBool false })
                     (perms
                     `{ "EX" <- ConstBool false }
                     `{ "SR" <- ConstBool false }
                     `{ "MC" <- ConstBool false }
                     `{ "LD" <- ConstBool false }
                     `{ "SL" <- ConstBool false }
                     `{ "LM" <- ConstBool false }
                     `{ "SD" <- ConstBool false }
                     `{ "LG" <- ConstBool false })))))).

    Definition encodePerms (perms: Expr ty CapPerms) : Expr ty (Array CapPermSz Bool) :=
      FromBit (Array CapPermSz Bool)
        ({< ToBit (perms`"GL"),
            ( ITE (And [perms`"EX"; perms`"LD"; perms`"MC"])
                {< ConstBit (2'b"01"), ToBit (perms`"SR"), ToBit (perms`"LM"), ToBit (perms`"LG") >}
                (ITE (And [perms`"LD"; perms`"MC"; perms`"SD"])
                   {< ConstBit (2'b"11"), ToBit (perms`"SL"), ToBit (perms`"LM"), ToBit (perms`"LG") >}
                   (ITE (And [perms`"LD"; perms`"MC"])
                      {< ConstBit (3'b"101"), ToBit (perms`"LM"), ToBit (perms`"LG") >}
                      (ITE (And [perms`"SD"; perms`"MC"])
                         (ConstBit (5'b"10000"))
                         (ITE (Or [perms`"LD"; perms`"SD"])
                            {< ConstBit (3'b"100"), ToBit (perms`"LD"), ToBit (perms`"SD") >}
                            {< ConstBit (2'b"00"), ToBit (perms`"U0"), ToBit (perms`"SE"),
                              ToBit (perms`"US") >}))))) >}).
  End CapPerms.

  Section Sealed.
    Definition unsealed : Expr ty (Bit CapOTypeSz) := ConstDef.
    Section testOType.
      Variable otype: Expr ty (Bit CapOTypeSz).
      Definition isSealed := isNotZero otype.
      Definition isNotSealed := isZero otype.
      Definition isForwardSentry := Or [Eq otype $1; Eq otype $2; Eq otype $3].
      Definition isBackwardSentry := Or [Eq otype $4; Eq otype $5].
      Definition isInterruptEnabling := Or [Eq otype $3; Eq otype $5].
      Definition isInterruptDisabling := Or [Eq otype $2; Eq otype $4].
      Definition isInterruptInheriting := Eq otype $1.
    End testOType.

    Section testAddr.
      Variable isExec: Expr ty Bool.
      Variable addr: Expr ty Addr.
      Definition isSealableAddr :=
        And [isZero (TruncMsb (AddrSz - CapOTypeSz) CapOTypeSz addr);
             Neq (TruncMsb 1 (CapOTypeSz - 1) (TruncLsb (AddrSz - CapOTypeSz) CapOTypeSz addr)) (ToBit isExec)].
    End testAddr.

    Definition createBackwardSentry (ie: Expr ty Bool) : Expr ty (Bit CapOTypeSz) := {< ConstBit 2'b"10", ToBit ie >}.
    Definition createForwardSentry (change ie: Expr ty Bool): Expr ty (Bit CapOTypeSz) :=
      {< ConstBit WO~0, ToBit change, ToBit ie >}.
  End Sealed.

  Section CapRelated.
    Definition get_E_from_cE (cE: Expr ty (Bit ExpSz)) : Expr ty (Bit ExpSz) := ITE (isAllOnes cE) $0 cE.
    Definition get_Mmsb_from_cE (cE: Expr ty (Bit ExpSz)) : Expr ty (Bit 1) := ToBit (isNotZero cE).
    Definition get_M_from_cE_cM (cE: Expr ty (Bit ExpSz)) (cM: Expr ty (Bit CapcMSz)) : Expr ty (Bit CapMSz) :=
      ({< get_Mmsb_from_cE cE, cM >}).

    Definition get_Mmsb_from_M (M: Expr ty (Bit CapMSz)) := TruncMsb 1 CapcMSz M.
    Definition get_cM_from_M (M: Expr ty (Bit CapMSz)) := TruncLsb 1 CapcMSz M.
    Definition get_cE_from_E_M (E: Expr ty (Bit ExpSz)) (M: Expr ty (Bit CapMSz)) :=
      ITE (And [isZero E; FromBit Bool (get_Mmsb_from_M M)]) (ConstBit (wones ExpSz)) E.
    Definition Emax := (Nat.pow 2 ExpSz - CapcMSz).
    Definition get_ECorrected_from_E (E: Expr ty (Bit ExpSz)) : Expr ty (Bit ExpSz) :=
      (ITE (Sge E $Emax) $Emax E).
    Definition get_E_from_ECorrected (ECorrected: Expr ty (Bit ExpSz)): Expr ty (Bit ExpSz) := ECorrected.
  End CapRelated.

  Section Representable.
    Variable base: Expr ty (Bit (AddrSz + 1)).
    Variable ECorrected: Expr ty (Bit ExpSz).

    Definition getRepresentableLimit :=
      Add [base; {< (Sll (ConstBit (ZToWord (AddrSz + 1 - CapMSz) 1)) ECorrected), ConstBit (wzero CapMSz) >}].
  End Representable.

  Section BaseLength.
    Definition BaseLength :=
      STRUCT_TYPE {
          "base"   :: Bit (AddrSz + 1);
          "length" :: Bit (AddrSz + 1) }.
    
    Variable addr: Expr ty Addr.
    Variable ECorrected: Expr ty (Bit ExpSz).
    Variable M: Expr ty (Bit CapMSz).
    Variable B: Expr ty (Bit CapBSz).

    Definition get_base_length_from_ECorrected_M_B : LetExpr ty BaseLength :=
      ( LetE aMidTop: Addr <- Srl addr ECorrected;
        LetE aMid: Bit CapBSz <- TruncLsb (AddrSz - CapBSz) CapBSz #aMidTop;
        LetE aTop: Bit (AddrSz - CapBSz) <- TruncMsb (AddrSz - CapBSz) CapBSz #aMidTop;
        LetE aHi <- ZeroExtendTo (AddrSz - CapBSz) (ToBit (Slt #aMid B));
        LetE base <- Sll (ZeroExtendTo (AddrSz + 1) ({< Sub #aTop #aHi, B >})) ECorrected;
        LetE length <- Sll (ZeroExtendTo (AddrSz + 1) M) ECorrected;
        @RetE _ BaseLength (STRUCT {
                                "base"   ::= #base;
                                "length" ::= #length })).
  End BaseLength.

  Section CalculateBounds.
    Variable base: Expr ty (Bit (AddrSz + 1)).
    Variable length: Expr ty (Bit (AddrSz + 1)).
    Variable IsSubset: Expr ty Bool.
    Variable IsFixedBase: Expr ty Bool.

    Local Notation shift_m_e sm m e :=
      (ITE (FromBit Bool (TruncMsb 1 sm m))
         (mkPair (Add [ZeroExtend 1 (TruncMsb sm 1 m); ZeroExtend sm (TruncLsb sm 1 m)]) (Add [e; $1]))
         (mkPair m e)).

    Local Notation shift_m_e_twice sm m e :=
      (LetE me: Pair (Bit (sm + 1)) (Bit ExpSz) <- shift_m_e sm m e;
       LetE m1e1: Pair (Bit (sm + 1)) (Bit ExpSz) <- shift_m_e sm (#me`"fst") (#me`"snd");
       @RetE _ (Pair (Bit sm) (Bit ExpSz))
         (STRUCT {
              "fst" ::= (TruncLsb 1 sm (#m1e1`"fst"));
              "snd" ::= (#m1e1`"snd") })) (sm in scope nat_scope).

    Definition Bounds :=
      STRUCT_TYPE {
          "E" :: Bit ExpSz;
          "cram" :: Bit (AddrSz + 1);
          "base" :: Bit (AddrSz + 1);
          "length" :: Bit (AddrSz + 1);
          "exact" :: Bool }.

    (* TODO check when length = 2^32-1 and base = 2^32-1 *)
    Definition calculateBounds : LetExpr ty Bounds :=
      ( LetE lenTrunc : Bit (AddrSz + 1 - CapBSz) <- TruncMsb (AddrSz + 1 - CapBSz) CapBSz length;
        LetE eInit: Bit ExpSz <- Add [$(AddrSz + 1 - CapBSz); Inv (countLeadingZeros _ #lenTrunc)];
        LetE e_lgCeilAdd1: Bool <- Or [isNotZero (TruncLsb (AddrSz + 1 - CapBSz) CapBSz length);
                                       (Neq (countOnes ExpSz #lenTrunc) $1)];
        LetE eLength: Bit ExpSz <-
                        Add [#eInit; ZeroExtendTo ExpSz (ToBit (ITE IsSubset (isZero #lenTrunc) #e_lgCeilAdd1))];
        LetE eBaseUncorrected : Bit (Nat.log2_up (AddrSz + 1)) <- countTrailingZeros _ base;
        LetE eBase <- TruncLsb 1 ExpSz (ITE (Sge #eBaseUncorrected $Emax) $Emax #eBaseUncorrected);
        LetE fixedBase_eBase_lt_eLength <- And [IsFixedBase; Slt #eBase #eLength];
        LetE e <- ITE #fixedBase_eBase_lt_eLength #eBase #eLength;
        LetE mask_e : Bit (AddrSz + 2 - CapBSz) <- Inv (Sll (ConstBit (wones (AddrSz + 2 - CapBSz))) #e);
        LetE base_mod_e : Bit (AddrSz + 2 - CapBSz) <-
                            Band [TruncLsb (CapBSz - 1) (AddrSz + 2 - CapBSz) base; #mask_e];
        LetE length_mod_e : Bit (AddrSz + 2 - CapBSz) <-
                              Band [TruncLsb (CapBSz - 1) (AddrSz + 2 - CapBSz) length; #mask_e];
        LetE sum_mod_e : Bit (AddrSz + 2 - CapBSz) <- Add [#base_mod_e; #length_mod_e];
        LetE iFloor : Bit 2 <- TruncLsb (AddrSz - CapBSz) 2 (Srl #sum_mod_e #e);
        LetE lost_sum : Bool <- isNotZero (Band [#sum_mod_e; #mask_e]);
        LetE iCeil : Bit 2 <- Add [#iFloor; ZeroExtendTo 2 (ToBit #lost_sum)];
        LetE d : Bit (CapBSz + 2) <- TruncLsb (AddrSz - 1 - CapBSz) (CapBSz + 2) (Srl length #e);
        LetE m : Bit (CapBSz + 2) <- Add [ITE #fixedBase_eBase_lt_eLength $(Nat.pow 2 CapMSz - 1) #d;
                                            ZeroExtend CapBSz (ITE IsSubset $0 #iCeil)];
        LETE m1e1: Pair (Bit (CapBSz + 1)) (Bit ExpSz) <- shift_m_e_twice (CapBSz + 1) #m #e;
        LETE m2e2: Pair (Bit CapBSz) (Bit ExpSz) <- shift_m_e_twice CapBSz (#m1e1`"fst") (#m1e1`"snd");
        LetE mf: Bit CapBSz <- #m2e2`"fst";
        LetE efUnsat: Bit ExpSz <- #m2e2`"snd";
        LetE isESaturated: Bool <- Sgt #efUnsat $(AddrSz + 1 - CapBSz);
        LetE ef <- ITE #isESaturated $(AddrSz + 1 - CapBSz) #efUnsat;
        LetE cram : Bit (AddrSz + 1) <- Sll (ConstBit (wones (AddrSz + 1))) #ef;
        LetE mask_ef : Bit (AddrSz + 1) <- Inv #cram;
        LetE lost_base : Bool <- isNotZero (Band [base; #mask_ef]);
        LetE outBase <-  Band [base; #cram];
        (* TODO for subset without fixed base.
           + (ZeroExtend Xlen (pack (IsSubset && #lost_base &&
           !(#isESaturated && ((base .& #cram) == #cram))))) << #ef *)
        LetE outLength: Bit (AddrSz + 1) <- Sll (ZeroExtendTo (AddrSz + 1) #mf) #ef;
        @RetE _ Bounds (STRUCT {
                            "E" ::= #ef;
                            "cram" ::= #cram;
                            "base" ::= #outBase;
                            "length" ::= #outLength;
                            "exact" ::= Or [#lost_base; Neq length #outLength] })).
  End CalculateBounds.

  Section EncodeCap.
    Variable ecap: Expr ty ECap.

    Definition encodeCap: LetExpr ty Cap :=
      ( LetE perms <- encodePerms (ecap`"perms");
        LetE E <- ecap`"E";
        LetE ECorrected <- get_ECorrected_from_E #E;
        LetE B <- TruncLsb (AddrSz + 1 - CapBSz) CapBSz (Sll (ecap`"base") #ECorrected);
        LetE T <- TruncLsb (AddrSz + 1 - CapBSz) CapBSz (Sll (ecap`"top") #ECorrected);
        LetE M <- Sub #T #B;
        @RetE _ Cap (STRUCT {
                         "R" ::= ecap`"R";
                         "p" ::= #perms;
                         "oType" ::= ecap`"oType";
                         "cE" ::= get_cE_from_E_M #E #M;
                         "cM" ::= get_cM_from_M #M;
                         "B" ::= #B })).
  End EncodeCap.

  Section DecodeCap.
    Variable cap: Expr ty Cap.
    Variable addr: Expr ty Addr.

    Definition decodeCap: LetExpr ty ECap :=
      ( LETE perms <- decodePerms (cap`"p");
        LetE E <- get_E_from_cE (cap`"cE");
        LetE ECorrected <- get_ECorrected_from_E #E;
        LETE base_length <- get_base_length_from_ECorrected_M_B addr #ECorrected
                              (get_M_from_cE_cM (cap`"cE") (cap`"cM")) (cap`"B");
        LetE base <- #base_length`"base";
        LetE length <- #base_length`"length";
        @RetE _ ECap (STRUCT {
                          "R" ::= cap`"R";
                          "perms" ::= #perms;
                          "oType" ::= cap`"oType";
                          "E" ::= #E;
                          "top" ::= Add [#base; #length];
                          "base" ::= #base })).
  End DecodeCap.
End Cap.

Definition Csrs := STRUCT_TYPE { "mcycle" :: Bit DXlen ;
                                  "mtime" :: Bit DXlen ;
                               "minstret" :: Bit DXlen ;
                                  "mshwm" :: Bit (Xlen - MshwmAlign) ;
                                 "mshwmb" :: Bit (Xlen - MshwmAlign) ;
                                  
                                     "ie" :: Bool ;
                              "interrupt" :: Bool ;
                                 "mcause" :: Bit McauseSz ;
                                  "mtval" :: Addr }.

Definition Scrs := STRUCT_TYPE {   "mtcc" :: FullECapWithTag ;
                                   "mtdc" :: FullECapWithTag ;
                              "mscratchc" :: FullECapWithTag ;
                                  "mepcc" :: FullECapWithTag }.

Definition Interrupts := STRUCT_TYPE { "mei" :: Bool ;
                                       "mti" :: Bool }.

Definition PcAluOut :=
  STRUCT_TYPE { "pcVal" :: Addr ;
      "BoundsException" :: Bool }.

Definition DecodeOut :=
  STRUCT_TYPE { "rs1Idx" :: Bit RegFixedIdSz;
                "rs2Idx" :: Bit RegFixedIdSz;
                 "rdIdx" :: Bit RegFixedIdSz;
                "decImm" :: Bit DecImmSz ;
                 "memSz" :: Bit MemSzSz ;

            "Compressed" :: Bool ;

           "ImmExtRight" :: Bool ;
            "ImmForData" :: Bool ;
            "ImmForAddr" :: Bool ;
 
              "ReadReg1" :: Bool ;
              "ReadReg2" :: Bool ;
              "WriteReg" :: Bool ;
 
            "MultiCycle" :: Bool ;
 
                "Src1Pc" :: Bool ;
               "InvSrc2" :: Bool ;
              "Src2Zero" :: Bool ;
                                  
                                  
        "ZeroExtendSrc1" :: Bool ;
                                  
                "Branch" :: Bool ;
              "BranchLt" :: Bool ;
             "BranchNeg" :: Bool ;
                   "Slt" :: Bool ;
                   "Add" :: Bool ;
                   "Xor" :: Bool ;
                    "Or" :: Bool ;
                                  
                                  
                   "And" :: Bool ;
                    "Sl" :: Bool ;
                    "Sr" :: Bool ;
                 "Store" :: Bool ;
                  "Load" :: Bool ;
          "LoadUnsigned" :: Bool ;
             "SetBounds" :: Bool ;
        "SetBoundsExact" :: Bool ;
          "BoundsSubset" :: Bool ;
       "BoundsFixedBase" :: Bool ;
   
           "CChangeAddr" :: Bool ;
                "AuiPcc" :: Bool ;
              "CGetBase" :: Bool ;
               "CGetTop" :: Bool ;
               "CGetLen" :: Bool ;
              "CGetPerm" :: Bool ;
              "CGetType" :: Bool ;
               "CGetTag" :: Bool ;
              "CGetHigh" :: Bool ;
                  "Cram" :: Bool ;
                  "Crrl" :: Bool ;
             "CSetEqual" :: Bool ;
           "CTestSubset" :: Bool ;
              "CAndPerm" :: Bool ;
             "CClearTag" :: Bool ;
              "CSetHigh" :: Bool ;
                 "CMove" :: Bool ;
                 "CSeal" :: Bool ;
               "CUnseal" :: Bool ;
     
                  "CJal" :: Bool ;
                 "CJalr" :: Bool ;
                "AuiAll" :: Bool ;
                   "Lui" :: Bool ;
   
            "CSpecialRw" :: Bool ;
                  "MRet" :: Bool ;
                 "ECall" :: Bool ;
                "EBreak" :: Bool ;
                "FenceI" :: Bool ;
                 "Fence" :: Bool ;
            "NotIllegal" :: Bool ;
   
                 "CsrRw" :: Bool ;
                "CsrSet" :: Bool ;
              "CsrClear" :: Bool ;
                "CsrImm" :: Bool }.

Definition AluIn :=
  STRUCT_TYPE {
             "pcAluOut" :: PcAluOut ;
            "decodeOut" :: DecodeOut ;
                 "regs" :: Array NumRegs FullECapWithTag ;
                "waits" :: Array NumRegs Bool ;
                 "csrs" :: Csrs ;
                 "scrs" :: Scrs ;
           "interrupts" :: Interrupts }.

Definition AluOut := STRUCT_TYPE { "regs" :: Array NumRegs FullECapWithTag ;
                                   "waits" :: Array NumRegs Bool ;
                                   "csrs" :: Csrs ;
                                   "scrs" :: Scrs ;
                                   "interrupts" :: Interrupts ;
                                   "ldRegIdx" :: Bit RegIdSz ;
                                   "memAddr" :: Addr ;
                                   "storeVal" :: FullECapWithTag ;
                                   "exception" :: Bool ; (* Note: For Branch Predictor *)
                                   "MRet" :: Bool ; (* Note: For Branch Predictor *)
                                   "Branch" :: Bool ; (* Note: For Branch Predictor *)
                                   "CJal" :: Bool ; (* Note: For Branch Predictor *)
                                   "CJalr" :: Bool ; (* Note: For Branch Predictor *)
                                   "LoadUnsigned" :: Bool ;
                                   "memSz" :: Bit MemSzSz ;
                                   "pcNotLinkAddrTagVal" :: Bool ;
                                   "pcNotLinkAddrCap" :: Bool ;
                                   "stall" :: Bool ;
                                   "Load" :: Bool ;
                                   "Store" :: Bool ;
                                   "FenceI" :: Bool }.

Section Decode.
  Variable ty: Kind -> Type.

  Variable inst: Expr ty Inst.

  Definition decodeFullInst: LetExpr ty DecodeOut :=
    ( LetE op: Bit 5 <- opcode inst;
      LetE f3: Bit 3 <- funct3 inst;
      LetE f7: Bit 7 <- funct7 inst;
      LetE f6: Bit 6 <- funct6 inst;
      LetE rdIdx: Bit RegFixedIdSz <- rdFixed inst;
      LetE rs1Idx: Bit RegFixedIdSz <- rs1Fixed inst;
      LetE rs2Idx: Bit RegFixedIdSz <- rs2Fixed inst;
      LetE immVal: Bit (snd immField) <- imm inst;

      LetE Lui: Bool <- Eq #op (ConstBit 5'b"01101");
      LetE AuiPcc: Bool <- Eq #op (ConstBit 5'b"00101");
      LetE AuiCgp: Bool <- Eq #op (ConstBit 5'b"11110");
      LetE CJal: Bool <- Eq #op (ConstBit 5'b"11011");
      LetE CJalr: Bool <- And [Eq #op (ConstBit 5'b"11001"); isZero #f3];
      LetE Branch: Bool <- And [Eq #op (ConstBit 5'b"11000"); Neq #f3`[2:1] (ConstBit 2'b"01")];

      LetE BranchLt: Bool <- FromBit Bool (#f3`[2:2]);
      LetE BranchNeg: Bool <- FromBit Bool (#f3`[0:0]);
      LetE BranchUnsigned: Bool <- FromBit Bool (#f3`[1:1]);

      LetE Load: Bool <- And [isZero #op; Not (isAllOnes #f3)];
      LetE Store: Bool <- And [Eq #op (ConstBit 5'b"01000"); Not (FromBit Bool (#f3`[2:2]))];

      LetE LoadUnsigned: Bool <- FromBit Bool (#f3`[2:2]);
      LetE memSz: Bit MemSzSz <- #f3`[1:0];

      LetE immediate: Bool <- Eq #op (ConstBit 5'b"00100");
      LetE nonImmediate: Bool <- Eq #op (ConstBit 5'b"01100");
      LetE addF3: Bool <- Eq #f3 $0;
      LetE sllF3: Bool <- Eq #f3 $1;
      LetE sltF3: Bool <- Eq #f3 $2;
      LetE sltuF3: Bool <- Eq #f3 $3;
      LetE xorF3: Bool <- Eq #f3 $4;
      LetE srF3: Bool <- Eq #f3 $5;
      LetE orF3: Bool <- Eq #f3 $6;
      LetE andF3: Bool <- Eq #f3 $7;
      LetE slF7: Bool <- isZero #f7;
      LetE sraSubF7: Bool <- Eq #f7 (ConstBit 7'b"0100000");
      LetE nonImmF7: Bool <- isZero #f7;

      LetE AddI: Bool <- And [#immediate; #addF3];
      LetE SltI: Bool <- And [#immediate; #sltF3];
      LetE SltuI: Bool <- And [#immediate; #sltuF3];
      LetE XorI: Bool <- And [#immediate; #xorF3];
      LetE OrI: Bool <- And [#immediate; #orF3];
      LetE AndI: Bool <- And [#immediate; #andF3];
      LetE SllI: Bool <- And [#immediate; #sllF3; #slF7];
      LetE SrlI: Bool <- And [#immediate; #srF3; #slF7];
      LetE SraI: Bool <- And [#immediate; #srF3; #sraSubF7];

      LetE AddOp: Bool <- And [#nonImmediate; #addF3; #nonImmF7];
      LetE SubOp: Bool <- And [#nonImmediate; #addF3; #sraSubF7];
      LetE SllOp: Bool <- And [#nonImmediate; #sllF3; #nonImmF7];
      LetE SltOp: Bool <- And [#nonImmediate; #sltF3; #nonImmF7];
      LetE SltuOp: Bool <- And [#nonImmediate; #sltuF3; #nonImmF7];
      LetE XorOp: Bool <- And [#nonImmediate; #xorF3; #nonImmF7];
      LetE SrlOp: Bool <- And [#nonImmediate; #srF3; #nonImmF7];
      LetE SraOp: Bool <- And [#nonImmediate; #srF3; #sraSubF7];
      LetE OrOp: Bool <- And [#nonImmediate; #orF3; #nonImmF7];
      LetE AndOp: Bool <- And [#nonImmediate; #andF3; #nonImmF7];

      LetE isFence: Bool <- Eq #op (ConstBit 5'b"00011");

      LetE Fence: Bool <- And [#isFence; isZero #f3];
      LetE FenceI: Bool <- And [#isFence; Eq #f3 $1];

      LetE isSys: Bool <- Eq #op (ConstBit 5'b"11100");

      LetE eHandle: Bool <- And [#isSys; isZero #f3; isZero #rdIdx; isZero #rs1Idx];
      LetE ECall: Bool <- And [#eHandle; isZero #f7; isZero #rs2Idx];
      LetE Wfi: Bool <- And [#eHandle; Eq #f7 (ConstBit 7'b"0001000"); Eq #rs2Idx (ConstBit 5'b"00101")];
      LetE EBreak: Bool <- And [#eHandle; isZero #f7; Eq #rs2Idx $1];
      LetE MRet: Bool <- And [#eHandle; Eq #f7 (ConstBit 7'b"0011000"); Eq #rs2Idx (ConstBit 5'b"00010")];

      LetE CsrRw: Bool <- And [#isSys; Eq (#f3`[1:0]) $1];
      LetE CsrSet: Bool <- And [#isSys; Eq (#f3`[1:0]) $2];
      LetE CsrClear: Bool <- And [#isSys; Eq (#f3`[1:0]) $3];

      LetE CsrImm: Bool <- And [#isSys; FromBit Bool (#f3`[2:2])];

      LetE cheriot: Bool <- Eq #op (ConstBit 5'b"10110");
      LetE cheriotNonImm: Bool <- Eq #cheriot (isZero #f3);
      LetE cheriot1Src: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"7f")];

      LetE CGetPerm: Bool <- And [#cheriot1Src; Eq #rs2Idx $0];
      LetE CGetType: Bool <- And [#cheriot1Src; Eq #rs2Idx $1];
      LetE CGetBase: Bool <- And [#cheriot1Src; Eq #rs2Idx $2];
      LetE CGetLen: Bool <- And [#cheriot1Src; Eq #rs2Idx $3];
      LetE CGetTag: Bool <- And [#cheriot1Src; Eq #rs2Idx $4];
      LetE CGetAddr: Bool <- And [#cheriot1Src; Eq #rs2Idx (ConstBit 5'h"f")];
      LetE CGetHigh: Bool <- And [#cheriot1Src; Eq #rs2Idx (ConstBit 5'h"17")];
      LetE CGetTop: Bool <- And [#cheriot1Src; Eq #rs2Idx (ConstBit 5'h"18")];

      LetE CSeal: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"b")];
      LetE CUnseal: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"c")];
      LetE CAndPerm: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"d")];
      
      LetE CSetAddr: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"10")];
      LetE CIncAddr: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"11")];
      LetE CIncAddrImm: Bool <- And [#cheriot; Eq #f3 $1];
      
      LetE CSetBounds: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"8")];
      LetE CSetBoundsExact: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"9")];
      LetE CSetBoundsRoundDown: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"a")];
      LetE CSetBoundsImm: Bool <- And [#cheriot; Eq #f3 $2; Eq #f7 (ConstBit 7'h"8")];

      LetE CSetHigh: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"16")];
      LetE CClearTag: Bool <- And [#cheriot1Src; Eq #rs2Idx (ConstBit 5'h"b")];

      LetE CSub: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"14")];
      LetE CMove: Bool <- And [#cheriot1Src; Eq #rs2Idx (ConstBit 5'h"a")];
      
      LetE CTestSubset: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"20")];
      LetE CSetEqual: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"21")];

      LetE CSpecialRw: Bool <- And [#cheriotNonImm; Eq #f7 (ConstBit 7'h"1")];

      LetE Crrl: Bool <- And [#cheriot1Src; Eq #rs2Idx $8];
      LetE Cram: Bool <- And [#cheriot1Src; Eq #rs2Idx $9];

      LetE MultiCycle: Bool <- #Load;

      LetE Src1Pc: Bool <- Or [#CJal; #Branch; #AuiPcc];
      LetE InvSrc2: Bool <- Or [#SltI; #SltuI; #SltOp; #SltuOp; #SubOp; #CSub; #CGetLen];
      LetE Src2Zero: Bool <- Or [#CSetAddr; #CGetAddr; #CSetHigh; #CAndPerm; #CClearTag;
                                 #CMove; #CSeal; #CUnseal; #CSetBounds; #CSetBoundsExact;
                                 #CSetBoundsRoundDown; #CSetBoundsImm];

      LetE ZeroExtendSrc1: Bool <- Or [#SltuI; #SrlI; #SltuOp; #SrlOp; #BranchUnsigned; #AuiPcc;
                                       #CIncAddr; #CIncAddrImm; #CSetAddr];
      LetE SltAll: Bool <- Or [#SltI; #SltuI; #SltOp; #SltuOp];
      LetE AddAll: Bool <- Or [#AddI; #AddOp; #SubOp; #CIncAddr; #CIncAddrImm; #CSetAddr; #CSub];
      LetE XorAll: Bool <- Or [#XorI; #XorOp];
      LetE  OrAll: Bool <- Or [#OrI; #OrOp; #CGetAddr; #CSetHigh; #CAndPerm; #CClearTag; #CMove; #CSeal;
                               #CUnseal; #CSetBounds; #CSetBoundsExact; #CSetBoundsRoundDown; #CSetBoundsImm];
      LetE AndAll: Bool <- Or [#AndI; #AndOp];
      LetE  SlAll: Bool <- Or [#SllI; #SllOp];
      LetE  SrAll: Bool <- Or [#SrlI; #SraI; #SrlOp; #SraOp];
      LetE SetBounds: Bool <- Or [#CSetBounds; #CSetBoundsExact; #CSetBoundsImm; #CSetBoundsRoundDown];
      LetE SetBoundsExact: Bool <- #CSetBoundsExact;
      LetE BoundsSubset: Bool <- #CSetBoundsRoundDown;
      LetE BoundsFixedBase: Bool <- #CSetBoundsRoundDown;

      LetE CChangeAddr: Bool <- Or [#CIncAddr; #CIncAddrImm; #CSetAddr; #AuiPcc];
      
      LetE isCsr: Bool <- And [#isSys; isNotZero (#f3`[1:0])];

      LetE SignExtendImmNoLoadNoCJalr <- Or [#AddI; #SltI; #XorI; #OrI; #AndI; #CIncAddrImm];
      LetE SignExtendImm: Bool <- Or [#SignExtendImmNoLoadNoCJalr; #Load; #CJalr];
      LetE ZeroExtendImm: Bool <- Or [#SltuI; #CSetBoundsImm; #SllI; #SrlI; #SraI];
      LetE AuiAll: Bool <- Or [#AuiPcc; #AuiCgp];

      LetE ECallAll: Bool <- Or [#ECall; #Wfi];

      LetE NotIllegal: Bool <- Or [#Lui; #AuiAll; #CJal; #CJalr; #Branch; #Load; #Store;
                                   #AddAll; #SltAll; #XorAll; #OrAll; #AndAll; #SlAll; #SrAll;
                                   #Fence; #FenceI; #ECallAll; #EBreak; #MRet; #isCsr;
                                   #CGetPerm; #CGetType; #CGetBase; #CGetLen;
                                   #CGetTag; #CGetHigh; #CGetTop;
                                   #CTestSubset; #CSetEqual;
                                   #CSpecialRw; #Crrl; #Cram];

      LetE ReadReg1: Bool <- Or [#AuiCgp; #CJalr; #Branch; #Load; #Store; #immediate; #nonImmediate;
                                 #isCsr; #cheriot];

      LetE ReadReg2: Bool <- Or [#Branch; #Store; #immediate;
                                 And [#cheriotNonImm; Not (Or [Eq #f7 (ConstBit 7'h"7f"); Eq #f7 $1])]];

      LetE WriteReg: Bool <- Or [#Lui; #AuiAll; #CJal; #CJalr; #Load; #immediate; #nonImmediate;
                                 #isCsr; #cheriot];

      LetE auiLuiOffsetInst: Bit Imm20Sz <- auiLuiOffset inst;

      LetE rs1Idx: Bit RegFixedIdSz <- rs1Fixed inst;
      LetE rs2Idx: Bit RegFixedIdSz <- rs2Fixed inst;
      LetE rdIdx: Bit RegFixedIdSz <- rdFixed inst;

      LetE decImm: Bit DecImmSz <- Or [ITE0 #SignExtendImm (SignExtendTo DecImmSz #immVal);
                                       ITE0 (Or [#ZeroExtendImm; #isCsr]) (ZeroExtendTo DecImmSz #immVal);
                                       ITE0 #Store (SignExtendTo DecImmSz ({< funct7 inst, rdFixed inst >}));
                                       ITE0 #Branch (SignExtendTo DecImmSz (branchOffset inst));
                                       ITE0 #CJal (jalOffset inst);
                                       ITE0 #AuiAll (SignExtend 1 #auiLuiOffsetInst);
                                       ITE0 #Lui ({<#auiLuiOffsetInst, ConstBit WO~0>})
                     ];
      
      LetE ImmExtRight: Bool <- Or [#AuiAll; #Lui];

      LetE ImmForData: Bool <- Or [#SignExtendImmNoLoadNoCJalr; #ZeroExtendImm; #AuiAll];
      LetE ImmForAddr: Bool <- Or [#Branch; #CJal; #CJalr; #Load; #Store];

      @RetE _ DecodeOut
        (STRUCT { "rs1Idx" ::= #rs1Idx ;
                  "rs2Idx" ::= #rs2Idx ;
                   "rdIdx" ::= #rdIdx ;
                  "decImm" ::= #decImm ;
                   "memSz" ::= #memSz ;

              "Compressed" ::= ConstTBool false;
             "ImmExtRight" ::= #ImmExtRight ;
              "ImmForData" ::= #ImmForData ;
              "ImmForAddr" ::= #ImmForAddr ;                           

                "ReadReg1" ::= #ReadReg1 ;
                "ReadReg2" ::= #ReadReg2 ;
                "WriteReg" ::= #WriteReg ;
        
              "MultiCycle" ::= #MultiCycle ;
        
                  "Src1Pc" ::= #Src1Pc ;
                 "InvSrc2" ::= #InvSrc2 ;
                "Src2Zero" ::= #Src2Zero ;
          "ZeroExtendSrc1" ::= #ZeroExtendSrc1 ;
                  "Branch" ::= #Branch ;
                "BranchLt" ::= #BranchLt ;
               "BranchNeg" ::= #BranchNeg ;
                     "Slt" ::= #SltAll ;
                     "Add" ::= #AddAll ;
                     "Xor" ::= #XorAll ;
                      "Or" ::= #OrAll ;
                     "And" ::= #AndAll ;
                      "Sl" ::= #SlAll ;
                      "Sr" ::= #SrAll ;
                   "Store" ::= #Store ;
                    "Load" ::= #Load ;
            "LoadUnsigned" ::= #LoadUnsigned ;
               "SetBounds" ::= #SetBounds ;
          "SetBoundsExact" ::= #SetBoundsExact ;
            "BoundsSubset" ::= #BoundsSubset ;
         "BoundsFixedBase" ::= #BoundsFixedBase ;
        
             "CChangeAddr" ::= #CChangeAddr ;
                  "AuiPcc" ::= #AuiPcc ;
                "CGetBase" ::= #CGetBase ;
                 "CGetTop" ::= #CGetTop ;
                 "CGetLen" ::= #CGetLen ;
                "CGetPerm" ::= #CGetPerm ;
                "CGetType" ::= #CGetType ;
                 "CGetTag" ::= #CGetTag ;
                "CGetHigh" ::= #CGetHigh ;
                    "Cram" ::= #Cram ;
                    "Crrl" ::= #Crrl ;
               "CSetEqual" ::= #CSetEqual ;
             "CTestSubset" ::= #CTestSubset ;
                "CAndPerm" ::= #CAndPerm ;
               "CClearTag" ::= #CClearTag ;
                "CSetHigh" ::= #CSetHigh ;
                   "CMove" ::= #CMove ;
                   "CSeal" ::= #CSeal ;
                 "CUnseal" ::= #CUnseal ;
        
                    "CJal" ::= #CJal ;
                   "CJalr" ::= #CJalr ;
                  "AuiAll" ::= #AuiAll ;
                     "Lui" ::= #Lui ;
        
              "CSpecialRw" ::= #CSpecialRw ;
                    "MRet" ::= #MRet ;
                   "ECall" ::= #ECallAll ;
                  "EBreak" ::= #EBreak ;
                  "FenceI" ::= #FenceI ;
                   "Fence" ::= #Fence ;
              "NotIllegal" ::= #NotIllegal ;
        
                   "CsrRw" ::= #CsrRw ;
                  "CsrSet" ::= #CsrSet ;
                "CsrClear" ::= #CsrClear ;
                  "CsrImm" ::= #CsrImm })).

  Definition decodeCompQ0: LetExpr ty DecodeOut :=
    ( LetE rdIdx: Bit RegFixedIdSz <- ZeroExtendTo RegFixedIdSz (inst`[4:2]);
      LetE rs2Idx: Bit RegFixedIdSz <- ZeroExtendTo RegFixedIdSz (inst`[4:2]);
      LetE f3: Bit 3 <- inst`[15:13];
      LetE CIncAddrImm: Bool <- isZero #f3;
      LetE rs1Idx: Bit RegFixedIdSz <- ITE #CIncAddrImm
                                         $sp
                                         (ZeroExtendTo RegFixedIdSz (inst`[9:7]));
      LetE memSz: Bit 2 <- #f3`[1:0];
      LetE Store: Bool <- FromBit Bool (#f3`[2:2]);
      LetE Load: Bool <- Not (Or [#Store; #CIncAddrImm]);
      LetE NotIllegal: Bool <- And [isNotZero (inst`[15:0]); Or [isZero #f3; FromBit Bool (#memSz`[1:1])]];
      LetE immMem_6_3: Bit 4 <- ({< (inst`[5:5]), (inst`[12:10]) >});
      LetE memDecImm <- ITE (FromBit Bool (#memSz`[0:0]))
                          ({<(inst`[6:6]), #immMem_6_3, ConstBit (wzero 3)>})
                          ({< (ConstBit WO~0), #immMem_6_3, (inst`[6:6]), ConstBit (wzero 2)>});
      LetE cIncImm <-  ({<(inst`[10:7]), (inst`[12:11]), (inst`[5:5]), (inst`[6:6]) , ConstBit (wzero 2)>});
      LetE decImm: Bit DecImmSz <- ITE #CIncAddrImm
                                     (SignExtendTo (ty := ty) DecImmSz #cIncImm)
                                     (SignExtendTo DecImmSz #memDecImm);
      @RetE _ DecodeOut
        (STRUCT { "rs1Idx" ::= #rs1Idx ;
                  "rs2Idx" ::= #rs2Idx ;
                   "rdIdx" ::= #rdIdx ;
                  "decImm" ::= #decImm ;
                   "memSz" ::= #memSz ;

              "Compressed" ::= ConstTBool true ;
             "ImmExtRight" ::= ConstTBool false ;
              "ImmForData" ::= #CIncAddrImm ;
              "ImmForAddr" ::= Not #CIncAddrImm ;

                "ReadReg1" ::= ConstTBool true ;
                "ReadReg2" ::= #Store ;
                "WriteReg" ::= Not #Store ;
       
              "MultiCycle" ::= #Load ;
       
                  "Src1Pc" ::= ConstTBool false ;
                 "InvSrc2" ::= ConstTBool false ;
                "Src2Zero" ::= ConstTBool false ;
          "ZeroExtendSrc1" ::= #CIncAddrImm ;
                  "Branch" ::= ConstTBool false ;
                "BranchLt" ::= ConstTBool false ;
               "BranchNeg" ::= ConstTBool false ;
                     "Slt" ::= ConstTBool false ;
                     "Add" ::= #CIncAddrImm ;
                     "Xor" ::= ConstTBool false ;
                      "Or" ::= ConstTBool false ;
                     "And" ::= ConstTBool false ;
                      "Sl" ::= ConstTBool false ;
                      "Sr" ::= ConstTBool false ;
                   "Store" ::= #Store ;
                    "Load" ::= #Load ;
            "LoadUnsigned" ::= ConstTBool false ;
               "SetBounds" ::= ConstTBool false ;
          "SetBoundsExact" ::= ConstTBool false ;
            "BoundsSubset" ::= ConstTBool false ;
         "BoundsFixedBase" ::= ConstTBool false ;
       
             "CChangeAddr" ::= #CIncAddrImm ;
                  "AuiPcc" ::= ConstTBool false ;
                "CGetBase" ::= ConstTBool false ;
                 "CGetTop" ::= ConstTBool false ;
                 "CGetLen" ::= ConstTBool false ;
                "CGetPerm" ::= ConstTBool false ;
                "CGetType" ::= ConstTBool false ;
                 "CGetTag" ::= ConstTBool false ;
                "CGetHigh" ::= ConstTBool false ;
                    "Cram" ::= ConstTBool false ;
                    "Crrl" ::= ConstTBool false ;
               "CSetEqual" ::= ConstTBool false ;
             "CTestSubset" ::= ConstTBool false ;
                "CAndPerm" ::= ConstTBool false ;
               "CClearTag" ::= ConstTBool false ;
                "CSetHigh" ::= ConstTBool false ;
                   "CMove" ::= ConstTBool false ;
                   "CSeal" ::= ConstTBool false ;
                 "CUnseal" ::= ConstTBool false ;
       
                    "CJal" ::= ConstTBool false ;
                   "CJalr" ::= ConstTBool false ;
                  "AuiAll" ::= ConstTBool false ;
                     "Lui" ::= ConstTBool false ;
       
              "CSpecialRw" ::= ConstTBool false ;
                    "MRet" ::= ConstTBool false ;
                   "ECall" ::= ConstTBool false ;
                  "EBreak" ::= ConstTBool false ;
                  "FenceI" ::= ConstTBool false ;
                   "Fence" ::= ConstTBool false ;
              "NotIllegal" ::= #NotIllegal ;
       
                   "CsrRw" ::= ConstTBool false ;
                  "CsrSet" ::= ConstTBool false ;
                "CsrClear" ::= ConstTBool false ;
                  "CsrImm" ::= ConstTBool false })).

  Definition decodeCompQ1: LetExpr ty DecodeOut :=
    ( LetE f3: Bit 3 <- inst`[15:13];
      LetE rs1Idx: Bit RegFixedIdSz <- ITE (FromBit Bool (#f3`[2:2]))
                                         (ZeroExtendTo RegFixedIdSz (inst`[9:7]))
                                         (ITE (Eq #f3`[1:0] $2) $c0 (inst`[11:7]));
      LetE rdIdx: Bit RegFixedIdSz <- ITE (FromBit Bool (#f3`[2:2]))
                                         (ITE (Eq #f3`[1:0] $1) $c0 (ZeroExtendTo RegFixedIdSz (inst`[9:7])))
                                         (inst`[11:7]);
      LetE rs2Idx: Bit RegFixedIdSz <- ITE (isNotZero (#f3`[1:0])) $0 (ZeroExtendTo RegFixedIdSz (inst`[4:2]));

      LetE AddI: Bool <- Or [isZero #f3; Eq #f3 $2];
      LetE CJal: Bool <- Eq (#f3`[1:0]) $1;

      LetE cjalImm: Bit DecImmSz <- SignExtendTo DecImmSz ({<inst`[12:12], inst`[8:8], inst`[10:9],
                                          inst`[6:6], inst`[7:7], inst`[2:2], inst`[11:11], inst`[5:3],
                                          ConstBit WO~0>});
      
      LetE CIncAddrImm: Bool <- And [Eq #f3 $3; Eq inst`[11:7] $2];

      LetE cIncImm: Bit DecImmSz <- SignExtendTo DecImmSz ({< inst`[12:12], inst`[4:3], inst`[5:5],
                                          inst`[2:2], inst`[6:6], ConstBit (wzero 4) >});

      LetE Lui: Bool <- And [Eq #f3 $3; Neq inst`[11:7] $2];

      LetE alu: Bool <- Eq #f3 $4;
      LetE someAlu: Bool <- Eq inst`[12:12] $0;

      LetE SrlI: Bool <- And [#alu; (isZero (inst`[11:10])); #someAlu];
      LetE SraI: Bool <- And [#alu; (Eq inst`[11:10] $1); #someAlu];
      LetE AndI: Bool <- And [#alu; Eq inst`[11:10] $2];

      LetE arith: Bool <- And [#alu; (Eq inst`[11:10] $3); #someAlu];

      LetE SubOp: Bool <- And [#arith; isZero (inst`[6:5])];
      LetE XorOp: Bool <- And [#arith; Eq inst`[6:5] $1];
      LetE  OrOp: Bool <- And [#arith; Eq inst`[6:5] $2];
      LetE AndOp: Bool <- And [#arith; Eq inst`[6:5] $3];

      LetE Branch: Bool <- isAllOnes (#f3`[2:1]);
      LetE BranchNeg: Bool <- FromBit Bool (#f3`[0:0]);

      LetE branchImm: Bit DecImmSz <- SignExtendTo DecImmSz ({<inst`[12:12], inst`[6:5],
                                            inst`[2:2], inst`[11:10], inst`[4:3], ConstBit WO~0 >});

      LetE normalImm: Bit 6 <- ({< inst`[12:12], inst`[6:2] >});

      LetE decImm: Bit DecImmSz <- caseDefault [(#CJal, #cjalImm);
                                                (#Branch, #branchImm);
                                                (#CIncAddrImm, #cIncImm);
                                                (#Lui, SignExtendTo DecImmSz ({<#normalImm, ConstBit WO~0>}))]
                                     (SignExtendTo (ty := ty) DecImmSz #normalImm);

      LetE ImmForData: Bool <- Or [#AddI; #CIncAddrImm; #Lui; #SrlI; #SraI; #AndI];
      LetE ImmForAddr: Bool <- Or [#CJal; #Branch];

      LetE ReadReg1: Bool <- Not (Or [#CJal; #Lui]);
      LetE ReadReg2: Bool <- And [Eq #f3 $4; Eq inst`[11:10] $3];
      LetE WriteReg: Bool <- Not #Branch;
      
      LetE NotIllegal: Bool <- And [Eq #f3 $4; Not (FromBit Bool (inst`[12:12]))];

      @RetE _ DecodeOut
        (STRUCT { "rs1Idx" ::= #rs1Idx ;
                  "rs2Idx" ::= #rs2Idx ;
                   "rdIdx" ::= #rdIdx ;
                  "decImm" ::= #decImm ;
                   "memSz" ::= Const ty (Bit MemSzSz) (wzero _) ;

              "Compressed" ::= ConstTBool true;
             "ImmExtRight" ::= #Lui ;
              "ImmForData" ::= #ImmForData ;
              "ImmForAddr" ::= #ImmForAddr ;

                "ReadReg1" ::= #ReadReg1 ;
                "ReadReg2" ::= #ReadReg2 ;
                "WriteReg" ::= #WriteReg ;
       
              "MultiCycle" ::= ConstTBool false ;
       
                  "Src1Pc" ::= Or [#CJal; #Branch] ;
                 "InvSrc2" ::= #SubOp ;
                "Src2Zero" ::= ConstTBool false ;
          "ZeroExtendSrc1" ::= #CIncAddrImm ;
                  "Branch" ::= #Branch ;
                "BranchLt" ::= ConstTBool false ;
               "BranchNeg" ::= #BranchNeg ;
                     "Slt" ::= ConstTBool false ;
                     "Add" ::= Or [#AddI; #CIncAddrImm; #SubOp] ;
                     "Xor" ::= #XorOp ;
                      "Or" ::= ConstTBool false ;
                     "And" ::= #AndOp ;
                      "Sl" ::= ConstTBool false ;
                      "Sr" ::= Or [#SrlI; #SraI] ;
                   "Store" ::= ConstTBool false ;
                    "Load" ::= ConstTBool false ;
            "LoadUnsigned" ::= ConstTBool false ;
               "SetBounds" ::= ConstTBool false ;
          "SetBoundsExact" ::= ConstTBool false ;
            "BoundsSubset" ::= ConstTBool false ;
         "BoundsFixedBase" ::= ConstTBool false ;
       
             "CChangeAddr" ::= #CIncAddrImm ;
                  "AuiPcc" ::= ConstTBool false ;
                "CGetBase" ::= ConstTBool false ;
                 "CGetTop" ::= ConstTBool false ;
                 "CGetLen" ::= ConstTBool false ;
                "CGetPerm" ::= ConstTBool false ;
                "CGetType" ::= ConstTBool false ;
                 "CGetTag" ::= ConstTBool false ;
                "CGetHigh" ::= ConstTBool false ;
                    "Cram" ::= ConstTBool false ;
                    "Crrl" ::= ConstTBool false ;
               "CSetEqual" ::= ConstTBool false ;
             "CTestSubset" ::= ConstTBool false ;
                "CAndPerm" ::= ConstTBool false ;
               "CClearTag" ::= ConstTBool false ;
                "CSetHigh" ::= ConstTBool false ;
                   "CMove" ::= ConstTBool false ;
                   "CSeal" ::= ConstTBool false ;
                 "CUnseal" ::= ConstTBool false ;
       
                    "CJal" ::= #CJal ;
                   "CJalr" ::= ConstTBool false ;
                  "AuiAll" ::= ConstTBool false ;
                     "Lui" ::= ConstTBool false ;
       
              "CSpecialRw" ::= ConstTBool false ;
                    "MRet" ::= ConstTBool false ;
                   "ECall" ::= ConstTBool false ;
                  "EBreak" ::= ConstTBool false ;
                  "FenceI" ::= ConstTBool false ;
                   "Fence" ::= ConstTBool false ;
              "NotIllegal" ::= #NotIllegal ;
       
                   "CsrRw" ::= ConstTBool false ;
                  "CsrSet" ::= ConstTBool false ;
                "CsrClear" ::= ConstTBool false ;
                  "CsrImm" ::= ConstTBool false })).

  Definition decodeCompQ2: LetExpr ty DecodeOut :=
    ( LetE f3: Bit 3 <- inst`[15:13];

      LetE rs2Idx: Bit RegFixedIdSz <- inst`[6:2];
      LetE rs1Idx: Bit RegFixedIdSz <- ITE (FromBit Bool (#f3`[1:1]))
                                         $sp
                                         (ITE (And [Eq #f3 $4; Not (FromBit Bool (inst`[12:12])); isNotZero #rs2Idx])
                                            $c0
                                            inst`[11:7]);
      LetE rdIdx: Bit RegFixedIdSz <- ITE (And [Eq #f3 $4; isZero #rs2Idx; Not (FromBit Bool (inst`[12:12]))])
                                        $c0
                                        (inst`[11:7]);
      
      LetE SllI: Bool <- isZero #f3;

      LetE Load: Bool <- Eq #f3`[2:1] $1;
      LetE Store: Bool <- Eq #f3`[2:1] $3;

      LetE memSz: Bit MemSzSz <- ({< ConstBit WO~1, (#f3`[0:0])>});

      LetE Add: Bool <- And [Eq #f3 $4; isNotZero #rs2Idx; isNotZero (inst`[11:7])];
      LetE CJalr: Bool <- And [Eq #f3 $4; isZero #rs2Idx; isNotZero (inst`[11:7])];
      LetE EBreak: Bool <- And [Eq #f3 $4; isZero #rs2Idx; isZero (inst`[11:7]); FromBit Bool (inst`[12:12])];

      LetE sllImm: Bit DecImmSz <- ZeroExtendTo DecImmSz #rs2Idx;
      LetE ldImm: Bit 9 <- ({< ITE0 (FromBit Bool (#f3`[0:0])) (inst`[4:4]), (inst`[3:2]), (inst`[12:12]),
                        (inst`[6:5]), ITE0 (Not (FromBit Bool (#f3`[0:0]))) (inst`[4:4]),
                        ConstBit (wzero 2) >});

      LetE stImm: Bit 9 <- ({< ITE0 (FromBit Bool (#f3`[0:0])) (inst`[9:9]), (inst`[8:7]), (inst`[12:10]),
                               ITE0 (Not (FromBit Bool (#f3`[0:0]))) (inst`[9:9]), ConstBit (wzero 2) >});

      LetE decImm: Bit DecImmSz <- Or [ITE0 #SllI #sllImm;
                                       ITE0 (Or [#Load; #Store]) (ZeroExtendTo DecImmSz (ITE #Load #ldImm #stImm))];

      LetE res: DecodeOut <-
                  STRUCT { "rs1Idx" ::= #rs1Idx ;
                           "rs2Idx" ::= #rs2Idx ;
                            "rdIdx" ::= #rdIdx ;
                           "decImm" ::= #decImm ;
                            "memSz" ::= #memSz ;

                       "Compressed" ::= ConstTBool true;
                      "ImmExtRight" ::= ConstTBool false ;
                       "ImmForData" ::= #SllI ;
                       "ImmForAddr" ::= Or [#Load; #Store; #CJalr] ;

                         "ReadReg1" ::= Not #EBreak ;
                         "ReadReg2" ::= And [FromBit Bool (#f3`[2:2]); Not #EBreak] ;
                         "WriteReg" ::= Not (Or [#EBreak; #Store]) ;
            
                       "MultiCycle" ::= ConstTBool false ;
            
                           "Src1Pc" ::= ConstTBool false ;
                          "InvSrc2" ::= ConstTBool false ;
                         "Src2Zero" ::= ConstTBool false ;
                   "ZeroExtendSrc1" ::= ConstTBool false ;
                           "Branch" ::= ConstTBool false ;
                         "BranchLt" ::= ConstTBool false ;
                        "BranchNeg" ::= ConstTBool false ;
                              "Slt" ::= ConstTBool false ;
                              "Add" ::= #Add ;
                              "Xor" ::= ConstTBool false ;
                               "Or" ::= ConstTBool false ;
                              "And" ::= ConstTBool false ;
                               "Sl" ::= #SllI ;
                               "Sr" ::= ConstTBool false ;
                            "Store" ::= #Store ;
                             "Load" ::= #Load ;
                     "LoadUnsigned" ::= ConstTBool false ;
                        "SetBounds" ::= ConstTBool false ;
                   "SetBoundsExact" ::= ConstTBool false ;
                     "BoundsSubset" ::= ConstTBool false ;
                  "BoundsFixedBase" ::= ConstTBool false ;
              
                      "CChangeAddr" ::= ConstTBool false ;
                           "AuiPcc" ::= ConstTBool false ;
                         "CGetBase" ::= ConstTBool false ;
                          "CGetTop" ::= ConstTBool false ;
                          "CGetLen" ::= ConstTBool false ;
                         "CGetPerm" ::= ConstTBool false ;
                         "CGetType" ::= ConstTBool false ;
                          "CGetTag" ::= ConstTBool false ;
                         "CGetHigh" ::= ConstTBool false ;
                             "Cram" ::= ConstTBool false ;
                             "Crrl" ::= ConstTBool false ;
                        "CSetEqual" ::= ConstTBool false ;
                      "CTestSubset" ::= ConstTBool false ;
                         "CAndPerm" ::= ConstTBool false ;
                        "CClearTag" ::= ConstTBool false ;
                         "CSetHigh" ::= ConstTBool false ;
                            "CMove" ::= ConstTBool false ;
                            "CSeal" ::= ConstTBool false ;
                          "CUnseal" ::= ConstTBool false ;
                
                             "CJal" ::= ConstTBool false ;
                            "CJalr" ::= #CJalr ;
                           "AuiAll" ::= ConstTBool false ;
                              "Lui" ::= ConstTBool false ;
              
                       "CSpecialRw" ::= ConstTBool false ;
                             "MRet" ::= ConstTBool false ;
                            "ECall" ::= ConstTBool false ;
                           "EBreak" ::= #EBreak ;
                           "FenceI" ::= ConstTBool false ;
                            "Fence" ::= ConstTBool false ;
                       "NotIllegal" ::= ConstTBool false ;
              
                            "CsrRw" ::= ConstTBool false ;
                           "CsrSet" ::= ConstTBool false ;
                         "CsrClear" ::= ConstTBool false ;
                           "CsrImm" ::= ConstTBool false };
      RetE #res).

  Definition decode : LetExpr ty DecodeOut :=
    ( LETE compQ0: DecodeOut <- decodeCompQ0;
      LETE compQ1: DecodeOut <- decodeCompQ1;
      LETE compQ2: DecodeOut <- decodeCompQ2;
      LETE fullInst: DecodeOut <- decodeFullInst;
      LetE instSz: Bit 2 <- TruncLsb (InstSz - 2) 2 inst;
      LetE res: DecodeOut <- ITE (FromBit Bool (#instSz`[1:1]))
                               (ITE (FromBit Bool (#instSz`[0:0]))
                                  #fullInst
                                  #compQ2)
                               (ITE (FromBit Bool (#instSz`[0:0]))
                                  #compQ1
                                  #compQ0);
      RetE #res).
End Decode.

Section Alu.
  Variable ty: Kind -> Type.

  (* Note: A single PCCap and tag exception when we have a superscalar processor;
     other values are repeated per lane *)
  Variable pcTag: Expr ty Bool.
  Variable pcCap: Expr ty ECap.

  Variable aluIn : Expr ty AluIn.
  
  Local Definition              pcVal: Expr ty Addr := aluIn`"pcAluOut"`"pcVal".
  Local Definition    BoundsException: Expr ty Bool := aluIn`"pcAluOut"`"BoundsException".
  
  Local Definition  regs: Expr ty (Array NumRegs _) := aluIn`"regs".
  Local Definition waits: Expr ty (Array NumRegs _) := aluIn`"waits".

  Local Definition               csrs: Expr ty Csrs := aluIn`"csrs".
  Local Definition      mcycle: Expr ty (Bit DXlen) := csrs`"mcycle".
  Local Definition       mtime: Expr ty (Bit DXlen) := csrs`"mtime".
  Local Definition    minstret: Expr ty (Bit DXlen) := csrs`"minstret".
  Local Definition           mshwm: Expr ty (Bit _) := csrs`"mshwm".
  Local Definition          mshwmb: Expr ty (Bit _) := csrs`"mshwmb".

  Local Definition                 ie: Expr ty Bool := csrs`"ie".
  Local Definition          interrupt: Expr ty Bool := csrs`"interrupt".
  Local Definition   mcause: Expr ty (Bit McauseSz) := csrs`"mcause".
  Local Definition              mtval: Expr ty Addr := csrs`"mtval".

  Local Definition               scrs: Expr ty Scrs := aluIn`"scrs".
  Local Definition    mtcc: Expr ty FullECapWithTag := scrs`"mtcc".
  Local Definition    mtdc: Expr ty FullECapWithTag := scrs`"mtdc".
  Local Definition              mscratch: Expr ty _ := scrs`"mscratchc" : Expr ty FullECapWithTag.
  Local Definition                 mepcc: Expr ty _ := scrs`"mepcc" : Expr ty FullECapWithTag.

  Local Definition   interrupts: Expr ty Interrupts := aluIn`"interrupts".
  Local Definition                mei: Expr ty Bool := interrupts`"mei".
  Local Definition                mti: Expr ty Bool := interrupts`"mti".

  Local Definition           rs1IdxFixed: Expr ty _ := aluIn`"decodeOut"`"rs1Idx" : Expr ty (Bit RegFixedIdSz).
  Local Definition           rs2IdxFixed: Expr ty _ := aluIn`"decodeOut"`"rs2Idx" : Expr ty (Bit RegFixedIdSz).
  Local Definition            rdIdxFixed: Expr ty _ := aluIn`"decodeOut"`"rdIdx" : Expr ty (Bit RegFixedIdSz).
  Local Definition   decImm: Expr ty (Bit DecImmSz) := aluIn`"decodeOut"`"decImm".
  Local Definition     memSz: Expr ty (Bit MemSzSz) := aluIn`"decodeOut"`"memSz".

  Local Definition         Compressed: Expr ty Bool := aluIn`"decodeOut"`"Compressed".
  Local Definition        ImmExtRight: Expr ty Bool := aluIn`"decodeOut"`"ImmExtRight".
  Local Definition         ImmForData: Expr ty Bool := aluIn`"decodeOut"`"ImmForData".
  Local Definition         ImmForAddr: Expr ty Bool := aluIn`"decodeOut"`"ImmForAddr".

  Local Definition           ReadReg1: Expr ty Bool := aluIn`"decodeOut"`"ReadReg1".
  Local Definition           ReadReg2: Expr ty Bool := aluIn`"decodeOut"`"ReadReg2".
  Local Definition           WriteReg: Expr ty Bool := aluIn`"decodeOut"`"WriteReg".

  Local Definition         MultiCycle: Expr ty Bool := aluIn`"decodeOut"`"MultiCycle".
  
  Local Definition             Src1Pc: Expr ty Bool := aluIn`"decodeOut"`"Src1Pc".
  Local Definition            InvSrc2: Expr ty Bool := aluIn`"decodeOut"`"InvSrc2".
  Local Definition           Src2Zero: Expr ty Bool := aluIn`"decodeOut"`"Src2Zero".
  Local Definition     ZeroExtendSrc1: Expr ty Bool := aluIn`"decodeOut"`"ZeroExtendSrc1".
  Local Definition             Branch: Expr ty Bool := aluIn`"decodeOut"`"Branch".
  Local Definition           BranchLt: Expr ty Bool := aluIn`"decodeOut"`"BranchLt".
  Local Definition          BranchNeg: Expr ty Bool := aluIn`"decodeOut"`"BranchNeg".
  Local Definition              SltOp: Expr ty Bool := aluIn`"decodeOut"`"Slt".
  Local Definition              AddOp: Expr ty Bool := aluIn`"decodeOut"`"Add".
  Local Definition              XorOp: Expr ty Bool := aluIn`"decodeOut"`"Xor".
  Local Definition               OrOp: Expr ty Bool := aluIn`"decodeOut"`"Or".
  Local Definition              AndOp: Expr ty Bool := aluIn`"decodeOut"`"And".
  Local Definition                 Sl: Expr ty Bool := aluIn`"decodeOut"`"Sl".
  Local Definition                 Sr: Expr ty Bool := aluIn`"decodeOut"`"Sr".
  Local Definition              Store: Expr ty Bool := aluIn`"decodeOut"`"Store".
  Local Definition               Load: Expr ty Bool := aluIn`"decodeOut"`"Load".
  Local Definition       LoadUnsigned: Expr ty Bool := aluIn`"decodeOut"`"LoadUnsigned".
  Local Definition          SetBounds: Expr ty Bool := aluIn`"decodeOut"`"SetBounds".
  Local Definition     SetBoundsExact: Expr ty Bool := aluIn`"decodeOut"`"SetBoundsExact".
  Local Definition       BoundsSubset: Expr ty Bool := aluIn`"decodeOut"`"BoundsSubset".
  Local Definition    BoundsFixedBase: Expr ty Bool := aluIn`"decodeOut"`"BoundsFixedBase".

  Local Definition        CChangeAddr: Expr ty Bool := aluIn`"decodeOut"`"CChangeAddr".
  Local Definition             AuiPcc: Expr ty Bool := aluIn`"decodeOut"`"AuiPcc".
  Local Definition           CGetBase: Expr ty Bool := aluIn`"decodeOut"`"CGetBase".
  Local Definition            CGetTop: Expr ty Bool := aluIn`"decodeOut"`"CGetTop".
  Local Definition            CGetLen: Expr ty Bool := aluIn`"decodeOut"`"CGetLen".
  Local Definition           CGetPerm: Expr ty Bool := aluIn`"decodeOut"`"CGetPerm".
  Local Definition           CGetType: Expr ty Bool := aluIn`"decodeOut"`"CGetType".
  Local Definition            CGetTag: Expr ty Bool := aluIn`"decodeOut"`"CGetTag".
  Local Definition           CGetHigh: Expr ty Bool := aluIn`"decodeOut"`"CGetHigh".
  Local Definition               Cram: Expr ty Bool := aluIn`"decodeOut"`"Cram".
  Local Definition               Crrl: Expr ty Bool := aluIn`"decodeOut"`"Crrl".
  Local Definition          CSetEqual: Expr ty Bool := aluIn`"decodeOut"`"CSetEqual".
  Local Definition        CTestSubset: Expr ty Bool := aluIn`"decodeOut"`"CTestSubset".
  Local Definition           CAndPerm: Expr ty Bool := aluIn`"decodeOut"`"CAndPerm".
  Local Definition          CClearTag: Expr ty Bool := aluIn`"decodeOut"`"CClearTag".
  Local Definition           CSetHigh: Expr ty Bool := aluIn`"decodeOut"`"CSetHigh".
  Local Definition              CMove: Expr ty Bool := aluIn`"decodeOut"`"CMove".
  Local Definition              CSeal: Expr ty Bool := aluIn`"decodeOut"`"CSeal".
  Local Definition            CUnseal: Expr ty Bool := aluIn`"decodeOut"`"CUnseal".
  
  Local Definition               CJal: Expr ty Bool := aluIn`"decodeOut"`"CJal".
  Local Definition              CJalr: Expr ty Bool := aluIn`"decodeOut"`"CJalr".
  Local Definition             AuiAll: Expr ty Bool := aluIn`"decodeOut"`"AuiAll".
  Local Definition                Lui: Expr ty Bool := aluIn`"decodeOut"`"Lui".

  Local Definition         CSpecialRw: Expr ty Bool := aluIn`"decodeOut"`"CSpecialRw".
  Local Definition               MRet: Expr ty Bool := aluIn`"decodeOut"`"MRet".
  Local Definition              ECall: Expr ty Bool := aluIn`"decodeOut"`"ECall".
  Local Definition             EBreak: Expr ty Bool := aluIn`"decodeOut"`"EBreak".
  Local Definition             FenceI: Expr ty Bool := aluIn`"decodeOut"`"FenceI".
  Local Definition              Fence: Expr ty Bool := aluIn`"decodeOut"`"Fence".
  Local Definition         NotIllegal: Expr ty Bool := aluIn`"decodeOut"`"NotIllegal".

  Local Definition              CsrRw: Expr ty Bool := aluIn`"decodeOut"`"CsrRw".
  Local Definition             CsrSet: Expr ty Bool := aluIn`"decodeOut"`"CsrSet".
  Local Definition           CsrClear: Expr ty Bool := aluIn`"decodeOut"`"CsrClear".
  Local Definition             CsrImm: Expr ty Bool := aluIn`"decodeOut"`"CsrImm".

  Local Notation GetCsrIdx x := (ConstBit (ZToWord CsrIdSz x)).

  Local Definition saturatedMax {n} (e: Expr ty (Bit (S n))) :=
    ITE (FromBit Bool (TruncMsb 1 n e)) (ConstBit (wones n)) (TruncLsb 1 n e).

  Local Definition exception (x: Expr ty (Bit CapExceptSz)) : Expr ty (Option (Bit CapExceptSz)) :=
    STRUCT { "valid" ::= ConstTBool true;
             "data" ::= x }.

  Local Definition regIdxWrong (idx: Expr ty (Bit RegFixedIdSz)) :=
    isNotZero (TruncMsb (RegFixedIdSz - RegIdSz) RegIdSz idx).

  Definition alu : LetExpr ty AluOut :=
    ( LetE rdIdx: Bit RegIdSz <- TruncLsb (RegFixedIdSz - RegIdSz) RegIdSz rdIdxFixed;
      LetE rs1Idx: Bit RegIdSz <- TruncLsb (RegFixedIdSz - RegIdSz) RegIdSz rs1IdxFixed;
      LetE rs2Idx: Bit RegIdSz <- TruncLsb (RegFixedIdSz - RegIdSz) RegIdSz rs2IdxFixed;
      LetE immVal: Bit Imm12Sz <- TruncLsb (DecImmSz - Imm12Sz) Imm12Sz decImm;
      LetE fullImmXlen <- ITE ImmExtRight ({< decImm, ConstBit (wzero 11) >}) (SignExtendTo Xlen decImm);
      LetE fullImmSXlen <- SignExtend 1 #fullImmXlen;

      LetE reg1 : FullECapWithTag <- ITE (isNotZero #rs1Idx) (regs @[ #rs1Idx ]) ConstDef;
      LetE tag1 : Bool <- #reg1`"tag";
      LetE cap1 : ECap <- #reg1`"ecap";
      LetE val1 : Addr <- #reg1`"addr";
      LetE reg2 : FullECapWithTag <- ITE (isNotZero #rs1Idx) (regs @[ #rs2Idx ]) ConstDef;
      LetE tag2 : Bool <- #reg2`"tag";
      LetE cap2 : ECap <- #reg2`"ecap";
      LetE val2 : Addr <- #reg2`"addr";

      LetE wait1 : Bool <- waits @[ #rs1Idx ];
      LetE wait2 : Bool <- waits @[ #rs2Idx ];

      LetE cap1Base <- #cap1`"base";
      LetE cap1Top <- #cap1`"top";
      LetE cap1Perms <- #cap1`"perms";
      LetE cap1OType <- #cap1`"oType";
      LetE cap2Base <- #cap2`"base";
      LetE cap2Top <- #cap2`"top";
      LetE cap2Perms <- #cap2`"perms";
      LetE cap2OType <- #cap2`"oType";
      LetE cap1NotSealed <- isNotSealed #cap1OType;
      LetE cap2NotSealed <- isNotSealed #cap2OType;

      LetE src1 <- ITE Src1Pc pcVal #val1;
      LetE src2Full <- ITE ImmForData
                         #fullImmSXlen
                         (SignExtend 1 (ITE0 (Not Src2Zero) #val2));
      LetE adderSrc1 <- ITE CGetLen #cap1Top
                          (ITE ZeroExtendSrc1 (ZeroExtend 1 #src1) (SignExtend 1 #src1));
      LetE adderSrc2 <- ITE CGetLen #cap1Base #src2Full;
      LetE adderSrc2Fixed <- ITE InvSrc2 (Inv #adderSrc2) #adderSrc2;
      LetE carryExt  <- ZeroExtend Xlen (ToBit InvSrc2);
      LetE adderResFull <- Add [#adderSrc1; #adderSrc2Fixed; #carryExt];
      LetE adderResZero <- isZero #adderResFull;
      LetE adderCarryBool <- FromBit Bool (TruncMsb 1 Xlen #adderResFull);
      LetE branchTakenPos <- ITE BranchLt #adderCarryBool #adderResZero;
      LetE branchTaken <- Xor [BranchNeg; #branchTakenPos];
      LetE adderRes: Data <- TruncLsb 1 Xlen #adderResFull;
      LetE src2 <- TruncLsb 1 Xlen #src2Full;
      LetE xorRes <- Bxor [#val1; #src2];
      LetE orRes <- Or [#val1; #src2];
      LetE andRes <- Band [#val1; #src2];
      LetE shiftAmt <- TruncLsb (Xlen - Nat.log2_up Xlen) (Nat.log2_up Xlen) #src2;
      LetE slRes <- Sll #val1 #shiftAmt;
      LetE srRes <- TruncLsb 1 Xlen (Sra #adderSrc1 #shiftAmt);

      LetE resAddrValFullTemp <- Add [ZeroExtend 1 #src1; ITE0 ImmForAddr #fullImmSXlen];
      LetE resAddrValFull <- {< TruncMsb Xlen 1 #resAddrValFullTemp,
          ITE CJalr (ConstBit WO~0) (TruncLsb Xlen 1 #resAddrValFullTemp) >};
      LetE resAddrVal <- TruncLsb 1 Xlen #resAddrValFull;
      LetE resAddrCarryBool <- FromBit Bool (TruncMsb 1 Xlen #resAddrValFull);

      LetE seal_unseal <- Or [CSeal; CUnseal];

      LetE load_store <- Or [Load; Store];
      LetE cjal_cjalr <- Or [CJal; CJalr];
      LetE branch_jump <- Or [Branch; #cjal_cjalr];
      LetE branch_jump_load_store <- Or [#branch_jump; #load_store];

      LetE change_addr <- Or [#branch_jump_load_store; CChangeAddr];

      LetE baseCheckBase <- caseDefault [(Src1Pc, pcCap`"base"); (#seal_unseal, #cap2Base)] #cap1Base;
      LetE baseCheckAddr <- caseDefault [(CSeal, ZeroExtend 1 #val2);
                                         (CUnseal, ZeroExtend (1 + Xlen - CapOTypeSz) #cap1OType);
                                         (#branch_jump_load_store, #resAddrValFull);
                                         (CTestSubset, #cap2Base)]
                              #adderResFull;
      LetE baseCheck <- And [Sle #baseCheckBase #baseCheckAddr;
                          Or [Not #change_addr; Not (FromBit Bool (TruncMsb 1 Xlen #baseCheckAddr))]];

      LetE representableLimit <- getRepresentableLimit
                                   (ITE Src1Pc (pcCap`"base") #cap1Base)
                                   (get_ECorrected_from_E (ITE Src1Pc (pcCap`"E") (#cap1`"E")));
      LetE topCheckTop <- caseDefault [(#seal_unseal, #cap2Top);
                                       (Or [#branch_jump; CChangeAddr], #representableLimit)]
                            #cap1Top;
      LetE topCheckAddr <-  caseDefault [(CSeal, ZeroExtend 1 #val2);
                                         (CUnseal, ZeroExtend (1 + Xlen - CapOTypeSz) #cap1OType);
                                         (#branch_jump_load_store, #resAddrValFull);
                                         (CTestSubset, #cap2Top)]
                              #adderResFull;
      LetE addrPlus <- ITE #load_store (Sll $1 memSz) (ZeroExtend Xlen (ToBit (Not CTestSubset)));
      LetE topCheckAddrFinal <- Add [#topCheckAddr; #addrPlus];
      LetE topCheck <-
        And [Sle #topCheckAddrFinal #topCheckTop;
             Or [Not (Or [#change_addr; CSeal; CUnseal]);
                 Not (FromBit Bool (TruncMsb 1 Xlen #topCheckAddrFinal));
                 isZero (TruncLsb 1 Xlen #topCheckAddrFinal)]];

      LetE boundsRes <- And [#baseCheck; #topCheck];
      
      LetE cTestSubset <- And [Eq #tag1 #tag2; #boundsRes;
                               Eq (Band [ToBit #cap1Perms; ToBit #cap2Perms]) (ToBit #cap2Perms)];

      LETE encodedCap <- encodeCap #cap1;
      LetE cram_crrl <- Or [Cram; Crrl];
      LetE boundsBase <- ZeroExtend 1 (ITE #cram_crrl $0 #val1);
      LetE boundsLength <- ZeroExtend 1 (ITE #cram_crrl #val1 #val2);
      LETE newBounds <- calculateBounds #boundsBase #boundsLength BoundsSubset BoundsFixedBase;
      LetE newBoundsTop <- Add [#newBounds`"base"; ##newBounds`"length"];
      LetE cSetEqual <- And [Eq #tag1 #tag2; Eq #cap1 #cap2; Eq #val1 #val2];
      LetE zeroExtendBoolRes <- ZeroExtendTo Xlen (ToBit (Or [ITE0 SltOp #adderCarryBool;
                                                              ITE0 CGetTag #tag1;
                                                              ITE0 CSetEqual #cSetEqual;
                                                              ITE0 CTestSubset #cTestSubset]));

      LetE cAndPermMask <- TruncLsb (Xlen - size CapPerms) (size CapPerms) #val2;
      LetE cAndPermCapPerms <- fixPerms (FromBit CapPerms (Band [ToBit #cap1Perms; #cAndPermMask]));
      LetE cAndPermCap <- #cap1 `{ "perms" <- #cAndPermCapPerms};
      LetE cAndPermTagNew <- Or [#cap1NotSealed;
                                 isAllOnes (ToBit ((FromBit CapPerms (#cAndPermMask))`{ "GL" <- ConstTBool true }))];

      LETE cSetHighCap <- decodeCap (FromBit Cap #val2) #val1;

      LetE cChangeAddrTagNew <- And [Or [Src1Pc; #cap1NotSealed]; #boundsRes];

      LetE cSealCap <- #cap1 `{ "oType" <- TruncLsb (AddrSz - CapOTypeSz) CapOTypeSz #val2};
      LetE cSealTagNew <- And [#tag2; #cap1NotSealed; #cap2NotSealed; (#cap2Perms`"SE"); #boundsRes;
                            isSealableAddr (##cap1Perms`"EX") #val1];

      LetE cUnsealCap <- ##cap1
        `{"oType" <- @unsealed ty }
        `{"perms" <- #cap1Perms`{ "GL" <- And [##cap1Perms`"GL"; ##cap2Perms`"GL"] } };
      LetE cUnsealTagNew <- And [#tag2; Not #cap1NotSealed; #cap2NotSealed; (#cap2Perms`"US"); #boundsRes];

      LetE cSetBoundsCap <- ##cap1
        `{ "E" <- ##newBounds`"E" }
        `{ "top" <- #newBoundsTop }
        `{ "base" <- #newBounds`"base" };

      LetE cJalJalrCap <- pcCap `{ "oType" <- ITE0 (Eq #rdIdx $ra) (createBackwardSentry ie) };
      LetE cJalrAddrCap <- #cap1 `{ "oType" <- unsealed ty};
      LetE newIe <- Or [And [CJalr; isInterruptEnabling #cap1OType];
                        And [ie; Not (And [CJalr; isInterruptDisabling #cap1OType])]];
      LetE notSealedOrInheriting <- Or [#cap1NotSealed; isInterruptInheriting #cap1OType];
      LetE cJalrSealedCond <-
        (ITE (Eq #rdIdx $c0)
           (ITE (Eq #rs1Idx $ra) (isBackwardSentry #cap1OType) #notSealedOrInheriting)
           (ITE (Eq #rdIdx $ra) (Or [#cap1NotSealed; isForwardSentry #cap1OType]) #notSealedOrInheriting));

      LetE isCsr <- Or [CsrRw; CsrSet; CsrClear];

      LetE validCsr <- Or [Eq #immVal (GetCsrIdx Mcycle);
                           Eq #immVal (GetCsrIdx Mtime);
                           Eq #immVal (GetCsrIdx Minstret);
                           Eq #immVal (GetCsrIdx Mcycleh);
                           Eq #immVal (GetCsrIdx Mtimeh);
                           Eq #immVal (GetCsrIdx Minstreth);
                           Eq #immVal (GetCsrIdx Mshwm);
                           Eq #immVal (GetCsrIdx Mshwmb);
                           Eq #immVal (GetCsrIdx Mstatus);
                           Eq #immVal (GetCsrIdx Mcause);
                           Eq #immVal (GetCsrIdx Mtval) ];

      LetE capSrException <- And [Or [CSpecialRw; MRet; And [#isCsr; #validCsr]];
                                  Not (pcCap`"perms"`"SR")];
      LetE isCapMem <- Eq memSz $LgNumBytesFullCapSz;
      LetE capNotAligned <- And [isNotZero (TruncLsb (AddrSz - LgNumBytesFullCapSz) LgNumBytesFullCapSz #resAddrVal);
                                 #isCapMem];
      LetE clcException <- And [Load; #capNotAligned];
      LetE cscException <- And [Store; #capNotAligned];

      LetE validScr <- Or [Eq rs2IdxFixed $Mtcc;
                           Eq rs2IdxFixed $Mtdc;
                           Eq rs2IdxFixed $Mscratchc;
                           Eq rs2IdxFixed $Mepcc ];

      LetE wrongRegId <- Or [And [ReadReg1; regIdxWrong rs1IdxFixed];
                             And [ReadReg2; regIdxWrong rs2IdxFixed];
                             And [WriteReg; regIdxWrong rdIdxFixed ]];

      LetE illegal <- Or [Not NotIllegal; And [#isCsr; Not #validCsr]; And [CSpecialRw; Not #validScr]; #wrongRegId];

      LetE capException <-
        (* Note: Kor is correct because of disjointness of capSrException with rest *)
        Or [ ITE0 #capSrException (exception $SrViolation) ;
             ITE (And [#load_store; Not #tag1]) (exception $TagViolation)
               (ITE (Or [And [#load_store; Not #cap1NotSealed];
                           And [CJalr; Or [Not #cJalrSealedCond; And [Not #cap1NotSealed; isNotZero #immVal]]]])
                  (exception $SealViolation)
                  (ITE (Or [And [CJalr; Not (#cap1Perms`"EX")]; And [Load; Not (##cap1Perms`"LD")];
                            And [Store; Not (##cap1Perms`"SD")]])
                     (exception (Or [ ITE0 (And [CJalr; Not (##cap1Perms`"EX")])
                                        (Const ty (Bit CapExceptSz) (natToWord _ ExViolation));
                                      ITE0 (And [Load; Not (##cap1Perms`"LD")])
                                        (Const ty (Bit CapExceptSz) (natToWord _ LdViolation));
                                      ITE0 (And [Store; Not (##cap1Perms`"SD")])
                                        (Const ty (Bit CapExceptSz) (natToWord _ SdViolation)) ]))
                     (ITE (And [Store; #isCapMem; Not (##cap1Perms`"MC")])
                        (exception $McSdViolation)
                        (ITE0 (And [#load_store; Not #boundsRes])
                           (exception $BoundsViolation) )))) ];

      LetE capExceptionVal <- #capException`"data";
      LetE isCapException <- #capException`"valid";
      LetE capExceptionSrc <- ITE0 (Not #capSrException) rs1IdxFixed;

      LetE isException <- Or [Not pcTag; BoundsException;
                              #illegal; EBreak; ECall; #clcException; #cscException; #isCapException];

      LetE mcauseExceptionVal: Bit McauseSz <- ITE (Or [Not pcTag; BoundsException])
                                                 $CapException
                                                 (caseDefault [ (#illegal, $IllegalException);
                                                                (EBreak, $EBreakException);
                                                                (ECall, $ECallException) ]
                                                    (caseDefault [ (#clcException, $LdAlignException);
                                                                   (#cscException, $SdAlignException) ]
                                                       (ITE0 #isCapException
                                                          (Const ty (Bit McauseSz) (natToWord _ CapException)))));

      LetE mtvalExceptionVal: Bit Xlen <-
                                ITE (Or [Not pcTag; BoundsException])
                                (ZeroExtendTo Xlen
                                   (Or [ITE0 (Not pcTag)
                                          (Const ty (Bit CapExceptSz) (natToWord _ TagViolation));
                                        ITE0 BoundsException
                                          (Const ty (Bit CapExceptSz) (natToWord _ BoundsViolation))]))
                                  (ITE0 (Not (Or [#illegal; EBreak; ECall]))
                                     (ITE (Or [#clcException; #cscException]) #resAddrVal
                                        (ITE0 #isCapException
                                           (ZeroExtendTo Xlen ({< #capExceptionSrc, #capExceptionVal >})))));


      LetE saturated <- saturatedMax
                          (Or [ITE0 CGetBase #cap1Base; ITE0 CGetTop #cap1Top; ITE0 CGetLen #adderResFull;
                               ITE0 Crrl (##newBounds`"length") ]);

      LetE linkAddr <- Add [pcVal; if HasComp then ITE Compressed $(InstSz/8) $(CompInstSz/8) else $(InstSz/8)];

      LetE resVal <- Or [ ITE0 AddOp #adderRes; ITE0 Lui #fullImmXlen;
                          ITE0 XorOp #xorRes; ITE0 OrOp #orRes; ITE0 AndOp #andRes;
                          ITE0 Sl #slRes; ITE0 Sr #srRes;
                          ITE0 CGetPerm (ZeroExtendTo Xlen (ToBit #cap1Perms));
                          ITE0 CGetType (ZeroExtendTo Xlen #cap1OType);
                          ITE0 CGetHigh (ToBit #encodedCap);
                          ITE0 #cjal_cjalr #linkAddr;
                          ITE0 Cram (TruncLsb 1 Xlen (##newBounds`"cram"));
                          #saturated;
                          #zeroExtendBoolRes];

      LetE resTag <- And [#tag1; Or [And [CAndPerm; #cAndPermTagNew];
                                     CMove;
                                     And [CChangeAddr; #cChangeAddrTagNew];
                                     And [CSeal; #cSealTagNew];
                                     ITE0 SetBounds (Or [Not SetBoundsExact; ##newBounds`"exact"]);
                                     And [CUnseal; #cUnsealTagNew];
                                     #cjal_cjalr ]];

      LetE resCap <- Or [ ITE0 CAndPerm #cAndPermCap;
                          ITE0 (Or [CClearTag; CMove; CChangeAddr]) (ITE Src1Pc pcCap #cap1);
                          ITE0 CSetHigh #cSetHighCap;
                          ITE0 SetBounds #cSetBoundsCap;
                          ITE0 #cjal_cjalr #cJalJalrCap;
                          ITE0 CSeal #cSealCap;
                          ITE0 CUnseal #cUnsealCap ];

      LetE csrIn <- ITE CsrImm (ZeroExtendTo Xlen rs1IdxFixed) #val1;

      LetE mcycleLsb : Bit Xlen <- TruncLsb Xlen Xlen mcycle;
      LetE mcycleMsb : Bit Xlen <- TruncMsb Xlen Xlen mcycle;
      LetE mtimeLsb : Bit Xlen <- TruncLsb Xlen Xlen mtime;
      LetE mtimeMsb : Bit Xlen <- TruncMsb Xlen Xlen mtime;
      LetE minstretLsb : Bit Xlen <- TruncLsb Xlen Xlen minstret;
      LetE minstretMsb : Bit Xlen <- TruncMsb Xlen Xlen minstret;
      LetE minstretInc : Bit DXlen <- Add [minstret; $1];
      LetE minstretIncLsb : Bit Xlen <- TruncLsb Xlen Xlen #minstretInc;
      LetE minstretIncMsb : Bit Xlen <- TruncMsb Xlen Xlen #minstretInc;

      LetE csrCurr <- Or [ ITE0 (Eq #immVal (GetCsrIdx Mcycle)) #mcycleLsb;
                           ITE0 (Eq #immVal (GetCsrIdx Mtime)) #mtimeLsb;
                           ITE0 (Eq #immVal (GetCsrIdx Minstret)) #minstretLsb;
                           ITE0 (Eq #immVal (GetCsrIdx Mcycleh)) #mcycleMsb;
                           ITE0 (Eq #immVal (GetCsrIdx Mtimeh)) #mtimeMsb;
                           ITE0 (Eq #immVal (GetCsrIdx Minstreth)) #minstretMsb;
                           ITE0 (Eq #immVal (GetCsrIdx Mshwm)) ({< mshwm, ConstBit (wzero MshwmAlign) >});
                           ITE0 (Eq #immVal (GetCsrIdx Mshwmb)) ({< mshwmb, ConstBit (wzero MshwmAlign) >});
                           ITE0 (Eq #immVal (GetCsrIdx Mstatus))
                             (ZeroExtendTo Xlen ({< ToBit ie, ConstBit (wzero (IeBit-1)) >}));
                           ITE0 (Eq #immVal (GetCsrIdx Mcause))
                             ({< ToBit interrupt, ZeroExtendTo (Xlen - 1) mcause >});
                           ITE0 (Eq #immVal (GetCsrIdx Mtval)) mtval ];

      LetE csrOut <- Or [ ITE0 CsrRw #csrIn;
                          ITE0 CsrSet (Or [#csrCurr; #csrIn]);
                          ITE0 CsrClear (Band [#csrCurr; Inv #csrIn]) ];

      LetE newMcycle: Bit DXlen <- ({< ITE (And [Not #isException; #isCsr; Eq #immVal (GetCsrIdx Mcycleh)])
                                         #csrOut
                                         #mcycleMsb,
                                       ITE (And [Not #isException; #isCsr; Eq #immVal (GetCsrIdx Mcycle)])
                                         #csrOut
                                         #mcycleLsb >});

      LetE newMtime: Bit DXlen <- ({< ITE (And [Not #isException; #isCsr; Eq #immVal (GetCsrIdx Mtimeh)])
                                        #csrOut
                                        #mtimeMsb,
                                      ITE (And [Not #isException; #isCsr; Eq #immVal (GetCsrIdx Mtime)])
                                        #csrOut
                                        #mtimeLsb >});

      LetE newMinstret: Bit DXlen <-
                          ITE #isException
                            minstret
                            ({< ITE (And [#isCsr; Eq #immVal (GetCsrIdx Minstreth)]) #csrOut #minstretIncMsb,
                                ITE (And [#isCsr; Eq #immVal (GetCsrIdx Minstret)])  #csrOut #minstretIncLsb >});

      LetE stAddrTrunc <- TruncLsb MshwmAlign (Xlen - MshwmAlign) #resAddrVal;
      LetE mshwmUpdCond <- And [Sge #stAddrTrunc mshwmb; Slt #stAddrTrunc mshwm];

      LetE newMshwm : Bit (Xlen - MshwmAlign) <- caseDefault
                        [(And [Not #isException; #isCsr; Eq #immVal (GetCsrIdx Mshwm)],
                           TruncLsb MshwmAlign (Xlen - MshwmAlign) #csrOut);
                         (And [Not #isException; Store; #mshwmUpdCond], #stAddrTrunc) ]
                           mshwm;

      LetE newMshwmb : Bit (Xlen - MshwmAlign) <- ITE (And [Not #isException; #isCsr; Eq #immVal (GetCsrIdx Mshwmb)])
                                                    (TruncLsb MshwmAlign (Xlen - MshwmAlign) #csrOut)
                                                    mshwmb;

      LetE ieBitSet <- FromBit Bool (TruncMsb 1 (IeBit - 1) (TruncLsb (Xlen - IeBit) IeBit #csrOut));
      LetE newIe : Bool <- caseDefault [(And [Not #isException; #isCsr; Eq #immVal (GetCsrIdx Mstatus)], #ieBitSet);
                                        (And [Not #isException; CJalr],
                                          Or [isInterruptEnabling #cap1OType;
                                              And [Not (isInterruptDisabling #cap1OType); ie]])]
                             ie;

      LetE newInterrupts : Interrupts <- STRUCT { "mei" ::= And [Not ie; mei] ;
                                                  "mti" ::= And [Or [Not ie; mei]; mti] };

      LetE newInterrupt : Bool <- And [ie; Or [mei; mti]];

      LetE newMcause : Bit McauseSz <- ITE (And [ie; mei])
                                         $Mei
                                         (ITE (And [ie; mti])
                                            $Mti
                                            (ITE #isException
                                               #mcauseExceptionVal
                                               (ITE (And [#isCsr; Eq #immVal (GetCsrIdx Mcause)])
                                                  (TruncLsb _ McauseSz #csrOut)
                                                  mcause)));

      LetE newMtval : Addr <- ITE #newInterrupt $0
                                (ITE #isException
                                   #mtvalExceptionVal
                                   (ITE (And [#isCsr; Eq #immVal (GetCsrIdx Mtval)]) #csrOut mtval));

      LetE newCsrs : Csrs <- STRUCT { "mcycle" ::= #newMcycle ;
                                      "mtime" ::= #newMtime ;
                                      "minstret" ::= #newMinstret ;
                                      "mshwm" ::= #newMshwm ;
                                      "mshwmb" ::= #newMshwmb ;
                                      "ie" ::= #newIe ;
                                      "interrupt" ::= #newInterrupt ;
                                      "mcause" ::= #newMcause ;
                                      "mtval" ::= #newMtval };

      LetE isScrWrite <- And [CSpecialRw; isNotZero rs1IdxFixed];
      LetE newMtdc <- ITE (And [Not #isException; #isScrWrite; Eq rs2IdxFixed $Mtdc]) #reg1 mtdc;
      LetE newMscratchc <- ITE (And [Not #isException; #isScrWrite; Eq rs2IdxFixed $Mscratchc]) #reg1 mscratch;
      
      LetE newTag <- And [#tag1;
                          (isZero (TruncLsb (Xlen - NumLsb0BitsInstAddr) NumLsb0BitsInstAddr #val1));
                          isNotSealed (#cap1`"oType");
                          ##cap1`"perms"`"EX"];

      LetE newCap <- ##reg1
        `{ "tag" <- #newTag }
        `{ "ecap" <- #cap1 }
        `{ "addr" <- ({< TruncMsb (Xlen - NumLsb0BitsInstAddr) NumLsb0BitsInstAddr
                           #val1, ConstBit (wzero NumLsb0BitsInstAddr) >}) };

      LetE newMepcc <- ITE #isException
                         (STRUCT { "tag" ::= And [pcTag; Not BoundsException];
                                   "ecap" ::= pcCap ;
                                   "addr" ::= pcVal (* + ITE0 (pcTag && !BoundsException && ECall) $(InstSz/8) *) })
                         (ITE (And [#isScrWrite; Eq rs2IdxFixed $Mepcc]) #newCap mepcc);

      LetE newMtcc <- ITE (And [Not #isException; #isScrWrite; Eq rs2IdxFixed $Mtcc]) #newCap mtcc;

      LetE newScrs : Scrs <- STRUCT { "mtcc" ::= #newMtcc ;
                                      "mtdc" ::= #newMtdc ;
                                      "mscratchc" ::= #newMscratchc ;
                                      "mepcc" ::= #newMepcc };

      LetE res : FullECapWithTag <- STRUCT { "tag" ::= #resTag;
                                             "ecap" ::= #resCap;
                                             "addr" ::= #resVal };

      LetE stall : Bool <- Or [ And [ReadReg1; #wait1];
                                And [ReadReg2; #wait2];
                                And [#isException; isNotZero (ToBit waits)]] ;

      LetE pcNotLinkAddrTagVal : Bool <- Or [#isException; MRet; And [Branch; #branchTaken]; CJal; CJalr];
      LetE pcNotLinkAddrCap : Bool <- Or [#isException; MRet; CJalr];

      LetE newPcTag : Bool <- ITE #isException
                                (mtcc`"tag")
                                (caseDefault [ (MRet, mepcc`"tag");
                                               (Or [And [Branch; #branchTaken]; CJal], #boundsRes);
                                               (CJalr, #tag1) ]
                                   pcTag) ;

      LetE newPcCap : ECap <- ITE #isException
                                (mtcc`"ecap")
                                (caseDefault [ (MRet, mepcc`"ecap");
                                               (CJalr, #cJalrAddrCap) ]
                                   pcCap) ;

      LetE newPcVal : Addr <- ITE #isException
                                (mtcc`"addr")
                                (caseDefault [ (MRet, mepcc`"addr");
                                               (Or [And [Branch; #branchTaken]; CJal; CJalr], #resAddrVal) ]
                                   #linkAddr ) ;

      LetE newPcc <- STRUCT { "tag" ::= #newPcTag ;
                              "ecap" ::= #newPcCap ;
                              "addr" ::=  #newPcVal };

      LetE newRegs : Array NumRegs FullECapWithTag <-
                       (regs @[ #rdIdx <- ITE (And [WriteReg; Not #isException] )
                                  #res
                                  (regs @[ #rdIdx]) ]) $[ 0 <- #newPcc ];

      LetE newWaits : Array NumRegs Bool <-
                        waits @[ #rdIdx <- And [MultiCycle; isNotZero #rdIdx; Not #isException] ];

      @RetE _ AluOut (STRUCT { "regs" ::= #newRegs ;
                               "waits" ::= #newWaits ;
                               "csrs" ::= #newCsrs ;
                               "scrs" ::= #newScrs ;
                               "interrupts" ::= #newInterrupts ;
                               "ldRegIdx" ::= #rdIdx ;
                               "memAddr" ::= #resAddrVal ;
                               "storeVal" ::= #reg2 ;
                               "exception" ::= #isException ;
                               "MRet" ::= And [MRet; Not #isException] ;
                               "Branch" ::= And [Branch; Not #isException] ;
                               "CJal" ::= And [CJal; Not #isException] ;
                               "CJalr" ::= And [CJalr; Not #isException] ;
                               "LoadUnsigned" ::= LoadUnsigned ;
                               "memSz" ::= memSz ;
                               "pcNotLinkAddrTagVal" ::= #pcNotLinkAddrTagVal ;
                               "pcNotLinkAddrCap" ::= #pcNotLinkAddrCap ;
                               "stall" ::= #stall ;
                               "Load" ::= And [Load; isNotZero #rdIdx; Not #isException] ;
                               "Store" ::= And [Store; Not #isException] ;
                               "FenceI" ::= And [FenceI; Not #isException] })).
End Alu.

(* TODO: Complete Spec, tools to convert assembly to Guru, MemBanks, Clut, Pipelines (Load, LoadCap, Store, Fetch) *)
