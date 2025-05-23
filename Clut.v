From Stdlib Require Import String List PeanoNat.
Require Import Guru.Lib.Word Guru.Lib.Library.
Require Import Guru.Syntax Guru.Notations Guru.Compiler Guru.Extraction.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Definition Xlen := 32.
Definition Addr := Bit Xlen.

Definition NumChannels := 4.

Definition PhyAddrSz := 22. (* 2-MB physical memory *)
Definition PseudoAddrSz := 25.  (* AXI address width size *)
Definition LgClutSz := Eval compute in (PseudoAddrSz - PhyAddrSz). (* Log of number of entries in the Clut *)

Definition PhyAddr := Bit PhyAddrSz.
Definition PseudoAddr := Bit PseudoAddrSz.
Definition ClutIdx := Bit LgClutSz.
Definition ClutSz := Eval compute in (Nat.pow 2 LgClutSz).

Section Clut.
  Variable ty: Kind -> Type.

  Local Open Scope guru.
  Local Open Scope string.

  Definition ClutEntry := STRUCT_TYPE {
                              "top" :: PhyAddr ;
                              "base" :: PhyAddr ;
                              "ReadPerm" :: Bool ;
                              "WritePerm" :: Bool }.

  Definition DmaReq := STRUCT_TYPE {
                           "addr" :: PseudoAddr ;
                           "size" :: PhyAddr ;
                           "isWrite" :: Bool }.

  Goal (size ClutEntry >= LgClutSz).
  Proof.
    cbv.
    Lia.lia.
  Qed.

  Goal (LgClutSz >= 1).
  Proof.
    cbv.
    Lia.lia.
  Qed.

  (* Command from Processor to insert or remove *)
  Definition Command := STRUCT_TYPE {
                            "clutEntry" :: ClutEntry ;
                            "isInsert"  :: Bool }.

  Definition clutIfc := {|modRegs := [
                            (* Keeps track if entry is used *)
                            ("valids", Build_Reg (Array ClutSz Bool) (Default _));
                            (* Keeps track of outstanding transactions *)
                            ("busys", Build_Reg (Array ClutSz Bool) (Default _));
                            (* Command from processor *)
                            ("procCommand", Build_Reg (Option Command) (Default _));
                            (* Response to processor *)
                            ("respToProc", Build_Reg (Option (Bit (LgClutSz + 1))) (Default _))];
                          modMems := [];
                          modRegUs := [
                            (* All the entries *)
                            ("entries", Array ClutSz ClutEntry)];
                          modMemUs := [];
                          modSends := (* Response to DMA if it can access *)
                            repeat ("dmaCanAccess", Bool) NumChannels;
                          modRecvs := [
                            (* Return from a read memory transaction to clear busy bit *)
                            ("readMemResults", Array NumChannels (Option ClutIdx));
                            (* Request from DMA to check validity of access *)
                            ("dmaCheckAccess", Array NumChannels DmaReq)]|}.

  Definition cl := getModLists clutIfc.

  Definition commandFromProc: Action ty cl (Bit 0) :=
    ( RegRead valids <- "valids" in cl;
      RegRead busys <- "busys" in cl;
      RegRead optCommand <- "procCommand" in cl;
      RegRead optResp <- "respToProc" in cl;
      RegReadU entries <- "entries" in cl;

      (* Find an empty slot in freeIndex. Highest bit of freeIndex is 1 if no empty slot is found *)
      Let optFreeIndex: Bit (LgClutSz + 1) <- countTrailingZeros (LgClutSz + 1) (Inv (ToBit #valids));
      Let freeIndex: ClutIdx <- TruncLsb 1 LgClutSz #optFreeIndex;
      Let freeIndexValid: Bool <- Not (FromBit Bool (TruncMsb 1 LgClutSz #optFreeIndex));

      Let rmIndex : ClutIdx <-  TruncLsb (size ClutEntry - LgClutSz) LgClutSz (ToBit (#optCommand`"data"`"clutEntry"));

      LetIf dummy <- If (And [#optCommand`"valid"; Not (#optResp`"valid")]) Then (
          LetIf dummy <- If (#optCommand`"data"`"isInsert") Then (
              RegWrite "respToProc" in cl <- mkSome #optFreeIndex;
              LetIf dummy <- If (#freeIndexValid) Then (
                  RegWriteU "entries" in cl <- #entries@[ #freeIndex <- ##optCommand`"data"`"clutEntry"];
                  RegWrite "valids" in cl <- #valids@[ #freeIndex <- ConstBool true ];
                  Return ConstDef );
              Return #dummy )
            Else (
              LetIf dummy <- If (Not (#busys@[#rmIndex])) Then (
                  RegWrite "valids" in cl <- #valids@[ #freeIndex <- ConstBool false ];
                  RegWrite "respToProc" in cl <- mkSome $1;
                  Return ConstDef )
                Else (
                  RegWrite "respToProc" in cl <- mkSome $0;
                  Return ConstDef);
              Return #dummy
            );
          Return #dummy );
      Return #dummy).

  Section PerChannel.
    Variable channelIdA: FinArray NumChannels.
    Definition channelIdS := FinArray_to_FinStruct channelIdA (repeat_length ("dmaCanAccess", Bool) NumChannels).

    Theorem Bool_channelIdS: Bool = fieldK (ls := msends cl) channelIdS.
    Proof.
      unfold NumChannels, channelIdS in *.
      simpl.
      destruct channelIdA; auto.
      repeat (destruct f; auto).
    Qed.

    (* DMA checks if it can access a particular pseudo-address *)
    Definition dmaCheckAccess: Action ty cl (Bit 0) :=
      ( Get dmaReqs <- "dmaCheckAccess" in cl;
        Let dmaReq : DmaReq <- ReadArrayConst #dmaReqs channelIdA;
        (* Split the incoming address into Clut index and Physical address *)
        Let clutIdx: ClutIdx <- TruncMsb LgClutSz PhyAddrSz (#dmaReq`"addr");
        Let phyAddr: PhyAddr <- TruncLsb LgClutSz PhyAddrSz (#dmaReq`"addr");
        
        (* Read corresponding Clut Entry using Clut index *)
        RegReadU entries <- "entries" in cl;
        RegRead valids <- "valids" in cl;
        RegRead busys <- "busys" in cl;
        Let entry: ClutEntry <- #entries@[#clutIdx];
        Let valid: Bool <- #valids@[#clutIdx];

        (* Check for bounds: base <= addr <= top and perms *)
        Let bounds: Bool <- And [Sle (#entry`"base") #phyAddr; Sle (Add [#phyAddr; (#dmaReq`"size")]) (#entry`"top")];
        Let perms: Bool <- ITE (#dmaReq`"isWrite") (#entry`"WritePerm") (##entry`"ReadPerm");

        Let validAccess <- And [#valid; #bounds; #perms];
        LetIf dummy <- If #validAccess Then (
            Send (modLists := cl) channelIdS (match Bool_channelIdS in _ = Y return Expr ty Y with
                                              | eq_refl => ConstBool true
                                              end) (
                (* If it's a read transaction, mark as busy *)
                LetIf dummy <- If (Not (#dmaReq`"isWrite")) Then (
                    RegWrite "busys" in cl <- #busys@[#clutIdx <- ConstBool true];
                    Return ConstDef
                  );
                Return #dummy ));
        Return #dummy ).

    (* When a read from the bus returns, mark entry as not-busy *)
    Definition finishRead: Action ty cl (Bit 0) :=
      ( Get readResults <- "readMemResults" in cl;
        Let optReadResult : Option ClutIdx <- ReadArrayConst #readResults channelIdA;
        Let readResult: ClutIdx <- #optReadResult`"data";
        RegRead valids <- "valids" in cl;
        RegRead busys <- "busys" in cl;

        LetIf dummy <- If (And [#optReadResult`"valid"; #valids@[#readResult]]) Then (
            RegWrite "busys" in cl <- #busys@[#readResult <- ConstBool false];
            Return ConstDef
          );
        Return #dummy).
  End PerChannel.
End Clut.
Definition clut: Mod := {|modDecl := clutIfc;
                          modActions := fun ty => commandFromProc ty ::
                                                    map (dmaCheckAccess ty) (genFinArray NumChannels) ++
                                                    map (finishRead ty) (genFinArray NumChannels) |}.

Definition compiledMod := compile clut.

Extraction "Compile" size genFinStruct genFinArray compiledMod.
