From Stdlib Require Import String List.
Require Import Guru.Library Guru.Syntax Guru.Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

(*
Section BankedMem.
  Variable LgNum8Banks: nat.
  Variable LgEachSize: nat.
  Variable memLists: ModLists.
  Variable p: FinArray 2.

  Local Definition LgNumBanks := LgNum8Banks + 3.
  Local Definition Num8Banks := Nat.pow 2 LgNum8Banks.
  Local Definition NumBanks := Nat.pow 2 LgNumBanks.
  Local Definition EachSize := Nat.pow 2 LgEachSize.
  Local Definition MemAddrSz := LgEachSize + LgNumBanks.
  Local Definition memRepeat := ("memBank"%string, Build_MemU EachSize (Bit 8) 2).
  Local Definition tagRepeat := ("tagBank"%string, Build_MemU EachSize Bool 2).

  Variable memEq : mmems memLists = repeat memRepeat NumBanks.
  Variable tagEq : mmemUs memLists = repeat tagRepeat Num8Banks.
  Variable initTagReg : FinStruct (mregs memLists).
  Variable initTagRegKind : fieldK initTagReg = Bit (1 + LgEachSize).

  Local Lemma num8BanksMinusPlus: Num8Banks - size Bool + size Bool = size (Array Num8Banks Bool).
  Proof.
    unfold Num8Banks; simpl.
    assert (Nat.pow 2 LgNum8Banks > 0) by (apply pow_2_n_gt_0).
    Lia.lia.
  Qed.
      
  Local Lemma portCast: forall memIdx: FinStruct (mmems memLists), FinArray 2 -> FinArray (memUPort (fieldK memIdx)).
  Proof.
    rewrite memEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma lineIdxCast: forall memIdx: FinStruct (mmems memLists),
      LgEachSize = Nat.log2_up (memUSize (fieldK memIdx)).
  Proof.
    rewrite memEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
    simpl.
    unfold EachSize.
    rewrite (Nat.log2_up_pow2 _ (Nat.le_0_l _)).
    reflexivity.
  Qed.

  Local Lemma valCast: forall memIdx: FinStruct (mmems memLists), Bit 8 = memUKind (fieldK memIdx).
  Proof.
    rewrite memEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma len_mmems_NumBanks: length (mmems memLists) = NumBanks.
  Proof.
    rewrite memEq.
    rewrite repeat_length.
    reflexivity.
  Qed.

  Local Lemma portCastTag: forall memIdx: FinStruct (mmemUs memLists),
      FinArray 2 -> FinArray (memUPort (fieldK memIdx)).
  Proof.
    rewrite tagEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma lineIdxCastTag: forall memIdx: FinStruct (mmemUs memLists),
      LgEachSize = Nat.log2_up (memUSize (fieldK memIdx)).
  Proof.
    rewrite tagEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
    simpl.
    unfold EachSize.
    rewrite (Nat.log2_up_pow2 _ (Nat.le_0_l _)).
    reflexivity.
  Qed.

  Local Lemma valCastTag: forall memIdx: FinStruct (mmemUs memLists), Bool = memUKind (fieldK memIdx).
  Proof.
    rewrite tagEq.
    intros.
    rewrite (fieldK_repeat memIdx); auto.
  Qed.

  Local Lemma len_mmems_NumBanks_tag: length (mmemUs memLists) = Num8Banks.
  Proof.
    rewrite tagEq.
    rewrite repeat_length.
    reflexivity.
  Qed.

  Section Ty.
    Variable ty: Kind -> Type.
    Variable addr: Expr ty (Bit MemAddrSz).
    Variable memSz: Expr ty (Bit (LgNumBanks)).
    Variable writeVals: Expr ty (Array NumBanks (Bit 8)).
    Variable isCap: Expr ty Bool.
    Variable tagVal: Expr ty Bool.

    Local Open Scope guru.

    Local Definition shamt := TruncLsb LgEachSize LgNumBanks addr.
    Local Definition lineIdx := TruncMsb LgEachSize LgNumBanks addr.

    Local Definition add1: Expr ty (Array NumBanks Bool) :=
      FromBit (Array NumBanks Bool)
        (castBits (@eq_sym _ _ _ (Nat.mul_1_r _)) (Inv (Sll (ConstBit (wones NumBanks)) shamt))).

    Local Definition castLineIdx (memIdx: FinStruct (mmems memLists)):
      Expr ty (Bit (Nat.log2_up (memUSize (fieldK (ls:=mmems memLists) memIdx)))) :=
      (Add [castBits (lineIdxCast memIdx) lineIdx;
            ITE0 (ReadArrayConst add1 (FinStruct_to_FinArray memIdx len_mmems_NumBanks))
              (ConstTBit (ZToWord (Nat.log2_up (memUSize (fieldK memIdx))) 1))]).

    Local Definition isWrites: Expr ty (Array NumBanks Bool) :=
      FromBit (Array NumBanks Bool)
        (castBits (@eq_sym _ _ _ (Nat.mul_1_r _)) (rotateLeft (Inv (Sll (ConstBit (wones NumBanks)) memSz)) shamt)).

    Local Definition rotWriteVals: Expr ty (Array NumBanks (Bit 8)) :=
      FromBit (Array NumBanks (Bit 8))
        (rotateLeft (ToBit writeVals) {< shamt, ConstDefK (Bit 3) >}).

    Local Definition doLoadRpNoRot : Action ty memLists (Array NumBanks (Bit 8)) :=
      fold_right (fun memIdx acc =>
                    ReadRpMem (modLists := memLists) "readMemRp" memIdx (portCast memIdx p)
                      (fun val =>
                         (LetA rest: Array NumBanks (Bit 8) <- acc;
                          Return (UpdateArrayConst #rest (FinStruct_to_FinArray memIdx len_mmems_NumBanks)
                                    (castBitsKind2 (valCast memIdx) #val)))))
        (Return ConstDef) (genFinStruct (mmems memLists)).

    Local Definition shamtTag := TruncMsb LgNum8Banks 3 shamt.

    Local Definition castLineIdxTag (tagIdx: FinStruct (mmemUs memLists)):
      Expr ty (Bit (Nat.log2_up (memUSize (fieldK (ls:=mmemUs memLists) tagIdx)))) :=
      castBits (lineIdxCastTag tagIdx) lineIdx.

    Local Definition tagBankCap: Expr ty (Array Num8Banks Bool) :=
      FromBit (Array Num8Banks Bool)
        (Sll (castBits num8BanksMinusPlus (ZeroExtendTo Num8Banks (ToBit isCap))) shamtTag).

    Local Definition tagBank: Expr ty (Array Num8Banks Bool) :=
      FromBit (Array Num8Banks Bool)
        (Sll (castBits num8BanksMinusPlus (ZeroExtendTo Num8Banks $1)) shamtTag).

    Definition doLoadRq : Action ty memLists (Bit 0) :=
      fold_right (fun memIdx acc =>
                    ReadRqMem (modLists := memLists) memIdx (castLineIdx memIdx) (portCast memIdx p) acc)
        (Return ConstDef) (genFinStruct (mmems memLists)).

    Definition doWrite : Action ty memLists (Bit 0) :=
      fold_right (fun memIdx acc =>
                    let arrayIdx: FinArray NumBanks := FinStruct_to_FinArray memIdx len_mmems_NumBanks in
                    (If (ReadArrayConst isWrites arrayIdx) Then (
                         WriteMem (modLists := memLists) memIdx (castLineIdx memIdx)
                           (castBitsKind1 (valCast memIdx) (ReadArrayConst rotWriteVals arrayIdx))
                           (Return (ConstDefK (Bit 0))));
                     acc))
        (Return ConstDef) (genFinStruct (mmems memLists)).

    Definition doLoadRp : Action ty memLists (Array NumBanks (Bit 8)) :=
      (LetA noRotLoadRp : Array NumBanks (Bit 8) <- doLoadRpNoRot;
       Return (FromBit (Array NumBanks (Bit 8))
                 (rotateRight (ToBit #noRotLoadRp) {< shamt, ConstDefK (Bit 3) >}))).

    Definition doLoadRqTag : Action ty memLists (Bit 0) :=
      fold_right (fun tagIdx acc =>
                    ReadRqMemU (modLists := memLists) tagIdx (castLineIdxTag tagIdx) (portCastTag tagIdx p) acc)
        (Return ConstDef) (genFinStruct (mmemUs memLists)).

    Definition doWriteTag : Action ty memLists (Bit 0) :=
      fold_right (fun tagIdx acc =>
                    (If (ReadArrayConst tagBankCap (FinStruct_to_FinArray tagIdx len_mmems_NumBanks_tag)) Then (
                         WriteMemU (modLists := memLists) tagIdx (castLineIdxTag tagIdx)
                           (match valCastTag tagIdx in _ = Y return Expr ty Y with
                            | eq_refl => tagVal
                            end)
                           (Return (ConstDefK (Bit 0))));
                     acc))
        (Return ConstDef) (genFinStruct (mmemUs memLists)).

    Definition doLoadRpTag : Action ty memLists Bool :=
      fold_right
        (fun tagIdx acc =>
           ReadRpMemU (modLists := memLists) "readTagRp" tagIdx (portCastTag tagIdx p)
             (fun val =>
                (LetA rest : Bool <- acc;
                 Return
                   (Or [And [ReadArrayConst tagBank (FinStruct_to_FinArray tagIdx len_mmems_NumBanks_tag);
                             match eq_sym (valCastTag tagIdx) in _ = Y return Expr ty Y with
                             | eq_refl => #val
                             end]; #rest]))))
        (Return ConstDef) (genFinStruct (mmemUs memLists)).

    Definition initTags : Action ty memLists (Bit 0) :=
      (ReadReg "initTagRegVal" initTagReg
         (fun initTagRegVal =>
            (let castInitTagRegVal: Expr ty (Bit (1 + LgEachSize)) :=
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
                   (genFinStruct (mmemUs memLists)));
             Return #dummy))).
  End Ty.
End BankedMem.
*)
