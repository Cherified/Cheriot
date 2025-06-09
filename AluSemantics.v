From Stdlib Require Import String List Zmod ZArith.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Notations Cheriot.Alu.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Set Printing Depth 1000.

Local Open Scope Z_scope.

Time
Definition evalCalculateBounds (base length: Expr type (Bit (AddrSz + 1))) (IsSubset IsFixedBase: Expr type Bool)
  : type Bounds :=
  Eval cbn beta delta iota in (evalLetExpr (calculateBounds base length IsSubset IsFixedBase)).

Time
Definition evalDecode (inst: Expr type Inst): type DecodeOut :=
  Eval cbn delta beta iota in (evalLetExpr (decode inst)).

Theorem evalDecodeRewrite (inst: Expr type Inst): evalDecode inst = evalLetExpr (decode inst).
Proof.
  unfold evalDecode.
  cbn delta beta iota.
  reflexivity.
Qed.

(*
Time
Definition evalAluValOnly (aluIn: Expr type AluIn) :=
  ltac:( let x := eval cbn delta beta iota in (evalLetExpr (aluValOnly aluIn)) in
           exact x).
  ltac:(let x := eval cbn delta beta iota in (evalLetExpr (aluValOnly1 aluIn)) in
          let x := eval cbv [getFinStruct getFinStructOption forceOption] in x in
            exact x).

Ltac evalSimpl x := 
  (let x := eval cbn delta [
                (* Syntax *)
                Neq Sub Slt Sgt Sle Sge castBits castBitsKind1 castBitsKind2 ConstExtract OneExtend
                  ZeroExtend SignExtend ZeroExtendTo SignExtendTo replicate isZero isNotZero UOr
                  isAllOnes UAnd rotateRight rotateLeft mkBoolArray countLeadingZerosArray
                  countTrailingZerosArray countOnesArray
                  (* Library *)
                  mapDiffTuple isEq Default
                  (* Semantics *)
                  evalExpr evalLetExpr evalFromBit evalOrBinary
                  (* readDiffTuple updDiffTuple readSameTuple updSameTuple updListLength *)
                  (* Alu Definitions *)
                  Xlen Data AddrSz Addr LgAddrSz ExpSz CapExceptSz
                  InstSz Inst CompInstSz CompInst HasComp NumLsb0BitsInstAddr
                  RegIdSz NumRegs RegFixedIdSz NumRegsFixed
                  Imm12Sz Imm20Sz DecImmSz
                  CapPermSz CapOTypeSz CapcMSz CapBSz CapMSz IeBit
                  BoundsViolation TagViolation SealViolation ExViolation LdViolation SdViolation
                  McSdViolation SrViolation IllegalException EBreakException LdAlignException SdAlignException
                  ECallException CapException McauseSz Mei Mti
                  Mcycle Mtime Minstret Mcycleh Mtimeh Minstreth Mshwm Mshwmb
                  Mstatus Mcause Mtval MshwmAlign CsrIdSz CsrId
                  Mtcc Mtdc Mscratchc Mepcc
                  DXlen MemSzSz FullCapSz NumBytesFullCapSz LgNumBytesFullCapSz
                  instSizeField opcodeField funct3Field funct7Field funct6Field immField
                  rs1Field rs2Field rdField rs1FixedField rs2FixedField rdFixedField auiLuiField
                  instSize opcode funct3 funct7 funct6 rs1 rs2 rd rs1Fixed rs2Fixed rdFixed c0 ra sp
                  imm branchOffset jalOffset auiLuiOffset isCompressed
                  (* Alu Caps *)
                  decodePerms fixPerms encodePerms
                  unsealed isSealed isNotSealed isForwardSentry isBackwardSentry
                  isInterruptEnabling isInterruptDisabling isInterruptInheriting
                  isSealableAddr createBackwardSentry createForwardSentry
                  get_E_from_cE get_Mmsb_from_cE get_M_from_cE_cM
                  get_Mmsb_from_M get_cM_from_M get_cE_from_E_M Emax get_ECorrected_from_E get_E_from_ECorrected
                  getRepresentableLimit get_base_length_from_ECorrected_M_B
                  calculateBounds encodeCap decodeCap
                  decodeFullInst decodeCompQ0 decodeCompQ1 decodeCompQ1
                  (* Zmod, Z, etc *)
                  Zmod.firstn Zmod_lastn Zmod.app Z.add Z.sub Zmod.of_Z Pos.add_carry Pos.succ Pos.add Z.sub_add
                  Z.opp Zmod.of_small_Z Z.pow_pos Pos.iter Z.mul Z.pos_sub Pos.pred_double
                  (* Misc *)
                  andb orb negb fold_left map fold_right fst snd
              ] beta iota in x in
     simplKind x).
*)
