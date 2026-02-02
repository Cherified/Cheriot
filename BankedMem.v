From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section BankedMem.
  Local Open Scope Z.
  (* Num8Banks and NumBanks used in Array and repeat; EachSize used in Array; rest should be Z *)
  Variable LgNum8Banks: Z. (* Lg of Number of 64-bit sized banks *)
  Variable LgEachSize: Z. (* Lg of Size of each bank *)
  Variable LgEachSizeGe0: LgEachSize >= 0.
  Variable memLists: ModLists.
  Variable port: FinType 2.

  Local Definition LgNumBanks := 3 + LgNum8Banks. (* Lg of Number of 8-bit sized banks *)
  Local Definition Num8Banks := Z.to_nat (Z.shiftl 1 LgNum8Banks).
  Local Definition NumBanks := Z.to_nat (Z.shiftl 1 LgNumBanks).
  Local Definition EachSize := Z.to_nat (Z.shiftl 1 LgEachSize).
  Local Definition MemAddrSz := LgNumBanks + LgEachSize.
  Local Definition memRepeat := ("memBank"%string, Build_MemU EachSize (Bit 8) 2).
  Local Definition tagRepeat := ("tagBank"%string, Build_MemU EachSize Bool 2).

  Variable memEq : memLists.(mmems) = repeat memRepeat NumBanks.
  Variable tagEq : memLists.(mmemUs) = repeat tagRepeat Num8Banks.
  Variable initTagReg : FinStruct memLists.(mregs).
  Variable initTagRegKind : fieldK initTagReg = Bit (LgEachSize + 1).

  Local Lemma NatZ_mul_1_r x: NatZ_mul x 1 = Z.of_nat x.
  Proof.
    induction x; simpl; auto.
    subst; Lia.lia.
  Qed.

  Local Open Scope Z.
  Local Lemma num8BanksMinusPlus: Z.of_nat Num8Banks - size Bool + size Bool = size (Array Num8Banks Bool).
  Proof.
    unfold size at 3.
    rewrite NatZ_mul_1_r.
    Lia.lia.
  Qed.
      
  Local Lemma portCast: forall memIdx: FinStruct memLists.(mmems), FinType 2 -> FinType (fieldK memIdx).(memUPort).
  Proof.
    rewrite memEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma LgEachSizeRoundTrip: LgEachSize = Z.log2_up (Z.of_nat EachSize).
  Proof.
    unfold EachSize.
    rewrite Z2Nat.id; rewrite Z.shiftl_1_l.
    - rewrite Z.log2_up_pow2 by Lia.lia.
      auto.
    - rewrite <- Z.pow_nonneg by Lia.lia.
      Lia.lia.
  Qed.


  Local Lemma lineIdxCast: forall memIdx: FinStruct memLists.(mmems),
      LgEachSize = Z.log2_up (Z.of_nat (fieldK memIdx).(memUSize)).
  Proof.
    rewrite memEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
    simpl.
    apply LgEachSizeRoundTrip.
  Qed.

  Local Lemma valCast: forall memIdx: FinStruct memLists.(mmems), Bit 8 = (fieldK memIdx).(memUKind).
  Proof.
    rewrite memEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma len_mmems_NumBanks: length memLists.(mmems) = NumBanks.
  Proof.
    rewrite memEq.
    rewrite repeat_length.
    reflexivity.
  Qed.

  Local Lemma portCastTag: forall memIdx: FinStruct memLists.(mmemUs),
      FinType 2 -> FinType (fieldK memIdx).(memUPort).
  Proof.
    rewrite tagEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma lineIdxCastTag: forall memIdx: FinStruct memLists.(mmemUs),
      LgEachSize = Z.log2_up (Z.of_nat (fieldK memIdx).(memUSize)).
  Proof.
    rewrite tagEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
    simpl.
    apply LgEachSizeRoundTrip.
  Qed.

  Local Lemma valCastTag: forall memIdx: FinStruct memLists.(mmemUs), Bool = (fieldK memIdx).(memUKind).
  Proof.
    rewrite tagEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma len_mmems_NumBanks_tag: length memLists.(mmemUs) = Num8Banks.
  Proof.
    rewrite tagEq.
    rewrite repeat_length.
    reflexivity.
  Qed.

  Section Ty.
    Variable ty: Kind -> Type.
    Variable addr: Expr ty (Bit MemAddrSz).
    Variable memSz: Expr ty (Bit LgNumBanks).
    Variable writeVals: Expr ty (Array (length memLists.(mmems)) (Bit 8)).
    Variable isCap: Expr ty Bool.
    Variable tagVal: Expr ty Bool.

    Local Open Scope guru.

    Local Definition shamt := TruncLsb LgEachSize LgNumBanks addr.
    Local Definition lineIdx := TruncMsb LgEachSize LgNumBanks addr.

    Local Definition add1: Expr ty (Array (length memLists.(mmems)) Bool) :=
      FromBit (Array (length (mmems memLists)) Bool) (Not (Sll (ConstBit (InvDefault _)) shamt)).

    Local Definition castLineIdx (memIdx: FinStruct memLists.(mmems)):
      Expr ty (Bit (Z.log2_up (Z.of_nat (memUSize (fieldK (ls:= memLists.(mmems)) memIdx))))) :=
      (Add [castBits (lineIdxCast memIdx) lineIdx;
            ITE0 (ReadArrayConst add1 memIdx)
              (ConstT (Bit (Z.log2_up (Z.of_nat (memUSize (fieldK (ls:=memLists.(mmems)) memIdx)))))
                 (Zmod.of_Z _ 1))]).

    Local Definition isWrites: Expr ty (Array (length memLists.(mmems)) Bool) :=
      FromBit (Array (length memLists.(mmems)) Bool)
        (rotateLeft (Not (Sll (ConstBit (InvDefault _)) memSz)) shamt).

    Local Definition rotWriteVals: Expr ty (Array (length memLists.(mmems)) (Bit 8)) :=
      FromBit (Array (length memLists.(mmems)) (Bit 8))
        (rotateLeft (ToBit writeVals) {< shamt, ConstDefK (Bit 3) >}).

    Local Definition doLoadRpNoRot : Action ty memLists (Array (length memLists.(mmems)) (Bit 8)) :=
      fold_right (fun memIdx acc =>
                    ReadRpMem (modLists := memLists) "readMemRp" memIdx (portCast memIdx port)
                      (fun val =>
                         (LetA rest: Array (length memLists.(mmems)) (Bit 8) <- acc;
                          Return (UpdateArrayConst #rest memIdx (castBitsKind2 (valCast memIdx) #val)))))
        (Return ConstDef) (genFinType (length memLists.(mmems))).

    Local Definition shamtTag := TruncMsb LgNum8Banks 3 shamt.

    Local Definition castLineIdxTag (tagIdx: FinStruct memLists.(mmemUs)):
      Expr ty (Bit (Z.log2_up (Z.of_nat (memUSize (fieldK (ls:=memLists.(mmemUs)) tagIdx))))) :=
      castBits (lineIdxCastTag tagIdx) lineIdx.

    Local Definition tagBankCap: Expr ty (Array (length memLists.(mmemUs)) Bool) :=
      FromBit (Array (length memLists.(mmemUs)) Bool)
        (Sll (ITE0 isCap (ConstT (Bit (NatZ_mul (length memLists.(mmemUs)) 1)) Zmod.one)) shamtTag).

    Local Definition tagBank: Expr ty (Array (length memLists.(mmemUs)) Bool) :=
      FromBit (Array (length memLists.(mmemUs)) Bool)
        (Sll (ConstT (Bit (NatZ_mul (length memLists.(mmemUs)) 1)) Zmod.one) shamtTag).

    Definition doLoadRq : Action ty memLists (Bit 0) :=
      fold_right (fun memIdx acc =>
                    ReadRqMem (modLists := memLists) memIdx (castLineIdx memIdx) (portCast memIdx port) acc)
        (Return ConstDef) (genFinType (length (mmems memLists))).

    Definition doWrite : Action ty memLists (Bit 0) :=
      fold_right (fun memIdx acc =>
                    If (ReadArrayConst isWrites memIdx) Then (
                        WriteMem (modLists := memLists) memIdx (castLineIdx memIdx)
                          (castBitsKind1 (valCast memIdx) (ReadArrayConst rotWriteVals memIdx))
                          (Return (ConstDefK (Bit 0))));
                  acc)
        (Return ConstDef) (genFinType (length (mmems memLists))).

    Definition doLoadRp : Action ty memLists (Array (length memLists.(mmems)) (Bit 8)) :=
      (LetA noRotLoadRp : Array (length memLists.(mmems)) (Bit 8) <- doLoadRpNoRot;
       Return (FromBit (Array (length memLists.(mmems)) (Bit 8))
                 (rotateRight (ToBit #noRotLoadRp) {< shamt, ConstDefK (Bit 3) >}))).

    Definition doLoadRqTag : Action ty memLists (Bit 0) :=
      fold_right (fun tagIdx acc =>
                    ReadRqMemU (modLists := memLists) tagIdx (castLineIdxTag tagIdx) (portCastTag tagIdx port) acc)
        (Return ConstDef) (genFinType (length (mmemUs memLists))).

    Definition doWriteTag : Action ty memLists (Bit 0) :=
      fold_right (fun tagIdx acc =>
                    (If (ReadArrayConst tagBankCap tagIdx) Then (
                         WriteMemU (modLists := memLists) tagIdx (castLineIdxTag tagIdx)
                           (match valCastTag tagIdx in _ = Y return Expr ty Y with
                            | eq_refl => tagVal
                            end)
                           (Return (ConstDefK (Bit 0))));
                     acc))
        (Return ConstDef) (genFinType (length (mmemUs memLists))).

    Definition doLoadRpTag : Action ty memLists Bool :=
      fold_right
        (fun tagIdx acc =>
           ReadRpMemU (modLists := memLists) "readTagRp" tagIdx (portCastTag tagIdx port)
             (fun val =>
                (LetA rest : Bool <- acc;
                 Return
                   (Or [And [ReadArrayConst tagBank tagIdx;
                             match eq_sym (valCastTag tagIdx) in _ = Y return Expr ty Y with
                             | eq_refl => #val
                             end]; #rest]))))
        (Return ConstDef) (genFinType (length (mmemUs memLists))).

    Definition initTags : Action ty memLists (Bit 0) :=
      (ReadReg "initTagRegVal" initTagReg
         (fun initTagRegVal =>
            (let castInitTagRegVal: Expr ty (Bit (LgEachSize + 1)) :=
               match initTagRegKind in _ = Y return Expr ty Y with
               | eq_refl => #initTagRegVal
               end in
             Let isDone : Bool <- FromBit Bool (TruncMsb 1 LgEachSize castInitTagRegVal);
             Let lineIdx : Bit LgEachSize <- TruncLsb 1 LgEachSize castInitTagRegVal;
             LetIf dummy <- If (Not #isDone) Then (
                 fold_right (fun tagIdx acc =>
                               WriteMemU (modLists := memLists) tagIdx (castBits (lineIdxCastTag tagIdx) #lineIdx)
                                 ConstDef acc)
                   (WriteReg initTagReg
                      (match eq_sym initTagRegKind in _ = Z return Expr ty Z with
                       | eq_refl => Add [castInitTagRegVal; $1]
                       end) (Return ConstDef))
                   (genFinType (length (mmemUs memLists))));
             Return #dummy))).
  End Ty.
End BankedMem.
