From Stdlib Require Import String List.
Require Import Guru.Library Guru.Syntax Guru.Notations.
Require Import Cheriot.Alu Cheriot.BankedMem Cheriot.Spec.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Pipeline.
  Local Open Scope guru_scope.
  Definition NumIssue := 1.

  Definition ExecRootPerms : type CapPerms := (STRUCT_CONST {
                                                   "U0" ::= false;
                                                   "SE" ::= false;
                                                   "US" ::= false;
                                                   "EX" ::= true;
                                                   "SR" ::= true;
                                                   "MC" ::= true;
                                                   "LD" ::= true;
                                                   "SL" ::= false;
                                                   "LM" ::= true;
                                                   "SD" ::= false;
                                                   "LG" ::= true;
                                                   "GL" ::= true }).

  Definition MemRootPerms : type CapPerms := (STRUCT_CONST {
                                                  "U0" ::= false;
                                                  "SE" ::= false;
                                                  "US" ::= false;
                                                  "EX" ::= false;
                                                  "SR" ::= false;
                                                  "MC" ::= true;
                                                  "LD" ::= true;
                                                  "SL" ::= true;
                                                  "LM" ::= true;
                                                  "SD" ::= true;
                                                  "LG" ::= true;
                                                  "GL" ::= true }).

  Definition SealRootPerms : type CapPerms := (STRUCT_CONST {
                                                   "U0" ::= true;
                                                   "SE" ::= true;
                                                   "US" ::= true;
                                                   "EX" ::= false;
                                                   "SR" ::= false;
                                                   "MC" ::= false;
                                                   "LD" ::= false;
                                                   "SL" ::= false;
                                                   "LM" ::= false;
                                                   "SD" ::= false;
                                                   "LG" ::= false;
                                                   "GL" ::= true }).

  Section Roots.
    Variable perms: type CapPerms.
    Definition createRootCap: type ECap :=
      (STRUCT_CONST {
           "R" ::= false ;
           "perms" ::= perms ;
           "oType" ::= Default (Bit _) ;
           "E" ::= natToWord _ Emax ;
           "top" ::= wconcat WO~1 (wzero AddrSz) ;
           "base" ::= wzero (AddrSz + 1) }).

    Definition createRoot: type FullECapWithTag :=
      (STRUCT_CONST {
           "tag" ::= true;
           "ecap" ::= createRootCap;
           "addr" ::= Default Addr }).
  End Roots.

  Definition ExecRoot := createRoot ExecRootPerms.
  Definition MemRoot := createRoot MemRootPerms.
  Definition SealRoot := createRoot SealRootPerms.

  Variable mtccVal : type Addr.
  
  Local Open Scope string_scope.

  Definition FetchOutElem := STRUCT_TYPE {
                                 "pcAluOut" ::= PcAluOut ;
                                 "inst" ::= Inst }.
  Definition FetchOut := STRUCT_TYPE {
                             "pcTag" :: Bool ;
                             "pcCap" :: ECap ;
                             "elems" :: Array NumIssue FetchOutElem }.

  Definition allRegs :=
    [ ("predPcVal", Build_Reg Addr (Default _));
      ("predPcCap", Build_Reg ECap (Default _));
      ("predPcTag", Build_Reg Bool (Default _));
      ("waits", Build_Reg (Array NumRegs Bool) (Default _));
      ("regs", Build_Reg (Array NumRegs FullECapWithTag) (Default _));
      ("csrs", Build_Reg Csrs (Default _));
      ("scrs", Build_Reg Scrs (STRUCT_CONST { "mtcc" ::= ExecRoot;
                                              "mtdc" ::= MemRoot;
                                              "mscratchc" ::= SealRoot;
                                              "mepcc" ::= ExecRoot}));
      ("interruptsReg", Build_Reg Interrupts (Default _))].
End Pipeline.
