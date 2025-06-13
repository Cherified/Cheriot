From Stdlib Require Import String List ZArith.
Require Import Guru.Library Guru.Syntax Guru.Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section ExprToRegAction.
  Variable ty: Kind -> Type.
  Variable k: Kind.
  Variable modLists: ModLists.
  Variable stateReg: FinStruct (mregs modLists).
  Variable stateRegKind: fieldK stateReg = k.
  
  Local Open Scope guru_scope.

  Section ActionOfExpr.
    Variable k2: Kind.
    Variable expr: Expr ty k -> Expr ty k2 -> Expr ty k.
    Definition actionOfExpr (e: Expr ty k2) : Action ty modLists (Bit 0) :=
      ReadReg "state" stateReg
        (fun state => WriteReg stateReg (match eq_sym stateRegKind in _ = Y return Expr ty Y with
                                         | eq_refl => expr (match stateRegKind in _ = Y return Expr ty Y with
                                                            | eq_refl => #state
                                                            end) e
                                         end) (Return ConstDef)).
  End ActionOfExpr.

  Section ActionOfUpdExpr.
    Variable expr: Expr ty k -> Expr ty k.
    Definition actionOfUpdExpr : Action ty modLists (Bit 0) :=
      ReadReg "state" stateReg
        (fun state => WriteReg stateReg (match eq_sym stateRegKind in _ = Y return Expr ty Y with
                                         | eq_refl => expr (match stateRegKind in _ = Y return Expr ty Y with
                                                            | eq_refl => #state
                                                            end)
                                         end) (Return ConstDef)).
  End ActionOfUpdExpr.

  Section ReadExpr.
    Variable k2: Kind.
    Variable expr: Expr ty k -> Expr ty k2.
    Definition readExpr : Action ty modLists k2 :=
      ReadReg "state" stateReg
        (fun state => Return (expr (match stateRegKind in _ = Y return Expr ty Y with
                                    | eq_refl => #state
                                    end))).
  End ReadExpr.
End ExprToRegAction.

Section Fifo.
  Variable capacity: nat.
  Variable k: Kind.

  Local Open Scope guru_scope.

  Definition FifoState := STRUCT_TYPE {
                              "elems" :: Array capacity k;
                              "size" :: Bit (Z.log2_up (Z.of_nat capacity)) }.

  Section Ty.
    Variable ty: Kind -> Type.

    Section Expr.
      Variable state: Expr ty FifoState.

      Definition isFullExpr : Expr ty Bool := Eq state`"size" $(Z.of_nat capacity).
      Definition isEmptyExpr : Expr ty Bool := Eq state`"size" $0.
      Definition enqExpr (v: Expr ty k): Expr ty FifoState :=
        ITE isFullExpr
          state
          (STRUCT { "elems" ::= state`"elems" @[ Add [state`"size"; $1] <- v];
                    "size" ::= Add [state`"size"; $1] }).
      Definition deqExpr: Expr ty FifoState :=
        ITE isEmptyExpr
          state
          (state `{"size" <- Sub state`"size" $1}).
    End Expr.

    Section Action.
      Variable modLists: ModLists.
      Variable stateReg: FinStruct (mregs modLists).
      Variable stateRegKind: fieldK stateReg = FifoState.

      Definition isFullAction: Action ty modLists Bool := readExpr stateRegKind isFullExpr.
      Definition isEmptyAction: Action ty modLists Bool := readExpr stateRegKind isEmptyExpr.
      Definition enqAction: Expr ty k -> Action ty modLists (Bit 0) := actionOfExpr stateRegKind enqExpr.
      Definition deqAction: Action ty modLists (Bit 0) := actionOfUpdExpr stateRegKind deqExpr.
    End Action.
  End Ty.
End Fifo.
