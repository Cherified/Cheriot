From Stdlib Require Import String List ZArith.
Require Import Guru.Library Guru.Syntax Guru.Notations Guru.Compiler Guru.Extraction.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Open Scope Z_scope.
Definition Xlen := 32.
Definition Addr := Bit Xlen.

Definition NumChannels := 4%nat.

Definition PhyAddrSz := 22. (* 2-MB physical memory *)
Definition PseudoAddrSz := 25.  (* AXI address width size *)
Definition LgClutSz := Eval compute in (PseudoAddrSz - PhyAddrSz). (* Log of number of entries in the Clut *)

Definition PhyAddr := Bit PhyAddrSz.
Definition PseudoAddr := Bit PseudoAddrSz.
Definition ClutIdx := Bit LgClutSz.
Definition ClutSz := Eval compute in (Z.shiftl 1 LgClutSz).

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
    discriminate.
  Qed.

  Goal (LgClutSz >= 1).
  Proof.
    cbv.
    discriminate.
  Qed.

  (* Command from Processor to insert or remove *)
  Definition Command := STRUCT_TYPE {
                            "clutEntry" :: ClutEntry ;
                            "isInsert"  :: Bool }.

  Definition ConfigReq := STRUCT_TYPE {
                              "offset"  :: Bit 2;
                              "value"   :: Bit Xlen;
                              "isWrite" :: Bool }.

  Definition LeftOverCommandSize := Eval compute in (size (Option Command) - Xlen).
  Definition RespToProcSize := Eval compute in size (Option (Bit (LgClutSz + 1))).

  Definition clutIfc := {|modRegs := [
                            (* Keeps track if entry is used *)
                            ("valids", Build_Reg (Array (Z.to_nat ClutSz) Bool) (Default _));
                            (* Keeps track of outstanding transactions *)
                            ("busys", Build_Reg (Array (Z.to_nat ClutSz) Bool) (Default _));
                            (* Command from processor split into two registers *)
                            ("procCommand1", Build_Reg (Bit Xlen) (Default _));
                            ("procCommand2", Build_Reg (Bit LeftOverCommandSize) (Default _));
                            (* Response to processor *)
                            ("respToProc", Build_Reg (Option (Bit (LgClutSz + 1))) (Default _))];
                          modMems := [];
                          modRegUs := [
                            (* All the entries *)
                            ("entries", Array (Z.to_nat ClutSz) ClutEntry)];
                          modMemUs := [];
                          modSends :=
                            ("respToProc", Bit Xlen) ::
                              (* Response to DMA if it can access the request received for DMA check access *)
                              repeat ("dmaCanAccess", Bool) NumChannels;
                          modRecvs := [
                            (* Config from processor *)
                            ("config", Option ConfigReq);
                            (* Return from a read memory transaction to clear busy bit *)
                            ("readMemResults", Array NumChannels (Option ClutIdx));
                            (* Request from DMA to check validity of access *)
                            ("dmaCheckAccess", Array NumChannels DmaReq)]|}.

  Definition cl := getModLists clutIfc.

  Definition commandFromProc: Action ty cl (Bit 0) :=
    ( RegRead valids <- "valids" in cl;
      RegRead busys <- "busys" in cl;
      RegRead procCommand1 <- "procCommand1" in cl;
      RegRead procCommand2 <- "procCommand2" in cl;
      RegRead optResp <- "respToProc" in cl;
      RegReadU entries <- "entries" in cl;
      Let optCommand : Option Command <- FromBit (Option Command) {< #procCommand2, #procCommand1 >};

      (* Find an empty slot in freeIndex. Highest bit of freeIndex is 1 if no empty slot is found *)
      Let optFreeIndex: Bit (LgClutSz + 1) <- countTrailingZerosArray (Not #valids) (LgClutSz + 1);
      Let freeIndex: ClutIdx <- TruncLsb 1 LgClutSz #optFreeIndex;
      Let freeIndexValid: Bool <- Not (FromBit Bool (TruncMsb 1 LgClutSz #optFreeIndex));

      Let rmIndex: ClutIdx <- TruncLsb (size ClutEntry - LgClutSz) LgClutSz (ToBit (#optCommand`"data"`"clutEntry"));

      LetIf dummy <- If (And [#optCommand`"valid"; Not (#optResp`"valid")]) Then (
          RegWrite "procCommand1" in cl <- ConstDef;
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

  (* This is the interface to configure the Clut from the processor, and to read the Clut responses to insert/delete*)
  Definition configFromProc: Action ty cl (Bit 0) :=
    ( RegRead procCommand1 <- "procCommand1" in cl;
      RegRead procCommand2 <- "procCommand2" in cl;
      RegRead respToProc <- "respToProc" in cl;
      Let optCommand : Option Command <- FromBit (Option Command) {< #procCommand2, #procCommand1 >};
      Get config <- "config" in cl;
      Let configData <- #config`"data";
      Let configOffset <- #configData`"offset";
      Let configValue <- #configData`"value";
      LetIf dummy <- If (#config`"valid") Then (
          LetIf dummy <- If (#configData`"isWrite") Then (
              LetIf dummy <- If (And [Not #optCommand`"valid"; isZero #configOffset]) Then (
                  RegWrite "procCommand1" in cl <- #configValue;
                  Return ConstDef )
                Else (
                  LetIf dummy <- If (And [Not #optCommand`"valid"; Eq #configOffset $1]) Then (
                      RegWrite "procCommand2"
                      in cl <- TruncLsb (Xlen - LeftOverCommandSize) LeftOverCommandSize #configValue;
                      Return ConstDef)
                    Else (
                      LetIf dummy <- If (#respToProc`"valid") Then (
                          RegWrite "respToProc"
                          in cl <- FromBit (Option (Bit (LgClutSz + 1)))
                               (TruncLsb (Xlen - RespToProcSize) RespToProcSize #configValue);
                          Return ConstDef );
                      Return #dummy);
                  Return #dummy);
              Return #dummy)
            Else (
              Put "respToProc" in cl <- (ITE (isZero #configOffset)
                                           #procCommand1
                                           (ITE (Eq #configOffset $1)
                                              (ZeroExtendTo Xlen #procCommand2)
                                              (ZeroExtendTo Xlen (ToBit #respToProc))));
              Return ConstDef
            );
          Return #dummy);
      Return #dummy).

  Section PerChannel.
    Variable channelIdA: FinType NumChannels.
    Definition channelIdS: FinStruct (msends cl) :=
      Build_FinType (n := S NumChannels) (S channelIdA.(finNum)) channelIdA.(finLt).
      
    Theorem Bool_channelIdS: Bool = fieldK (ls := msends cl) channelIdS.
    Proof.
      unfold NumChannels, channelIdS in *.
      destruct channelIdA;
        simpl; auto.
      do 4 (destruct finNum; auto).
      destruct finNum; contradiction.
    Qed.

    (* DMA checks if it can access a particular pseudo-address *)
    (* On read checks, it outputs true only if the there's no pending read transaction for the same entry *)
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
            (* If it's a read transaction, then it must not be already busy *)
            Send (modLists := cl) channelIdS (match Bool_channelIdS in _ = Y return Expr ty Y with
                                              | eq_refl => Or [#dmaReq`"isWrite"; Not #busys@[#clutIdx]]
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
                          modActions := fun ty => commandFromProc ty :: configFromProc ty ::
                                                    map (dmaCheckAccess ty) (genFinType NumChannels) ++
                                                    map (finishRead ty) (genFinType NumChannels) |}.

Definition compiledMod := compile clut.

Extraction "Compile" size genFinType finNum updList compiledMod.
