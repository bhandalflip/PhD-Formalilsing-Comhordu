(** * Consistency of the model axioms

    [ComhBasics] declares the protocol's model parameters as global [Axiom]s:
    the set of modes, fail-safety, the mode transition relation and its timing,
    message latency, maximum speed, minimum distances of compatibility, broadcast
    periods, and the constraints relating them. They are deliberately left
    uninterpreted, so that [safety] holds for every instantiation.

    Global axioms are only harmless if they can be satisfied together; otherwise
    [safety] would hold vacuously. This file shows they can be:

    - [ComhModel] bundles one field per axiom, in the order of [ComhBasics], each
      field stated in terms of the earlier fields instead of the global axioms.
    - [global_model] instantiates [ComhModel] with the global axioms themselves,
      so the record captures exactly those axioms
      ([Print Assumptions global_model] lists them).
    - [concrete_model] is an axiom-free inhabitant, so the axioms are jointly
      consistent relative to Rocq and the stdlib reals.
      [Print Assumptions concrete_model] shows no [ComhBasics] axiom.

    [concrete_model] is deliberately non-degenerate:
    - It has two modes: [Safe], which is fail-safe, and [Moving], which is not.
    - Every transition is permitted.
    - Two [Moving] entities must keep a positive distance (1) apart.

    So safety is a real constraint in this model, not something every
    configuration satisfies trivially. *)

From Stdlib Require Import Reals Lra.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.

Open Scope R_scope.

(** One field per axiom of [ComhBasics], in declaration order. *)
Record ComhModel := {
  cm_adaptNotif : Time;
  cm_msgLatency : Time;
  cm_speedMax : nonnegreal;
  cm_Mode : Type;
  cm_failSafe : cm_Mode -> Prop;
  cm_fsDecMode : forall m : cm_Mode, decidable (cm_failSafe m);
  cm_eqDecMode : eqDec cm_Mode;
  cm_modeTransRel : cm_Mode -> cm_Mode -> Prop;
  cm_modeTransRelDec : forall m1 m2 : cm_Mode,
    {cm_modeTransRel m1 m2} + {~ cm_modeTransRel m1 m2};
  cm_modeTransTime : forall m1 m2 : cm_Mode, cm_modeTransRel m1 m2 -> Time;
  cm_failSafeSucc : cm_Mode -> cm_Mode;
  cm_failSafeSuccFS : forall m : cm_Mode, cm_failSafe (cm_failSafeSucc m);
  cm_failSafeSucc_successor : forall m : cm_Mode, cm_modeTransRel m (cm_failSafeSucc m);
  cm_trans : cm_Mode -> Time;
  cm_transMax : Time;
  cm_waitSurplus : Delay;
  cm_transMaxBound : forall m : cm_Mode, cm_trans m <= cm_transMax;
  cm_minDistComp : cm_Mode -> cm_Mode -> Distance;
  cm_minDistCompSymmetric : forall m1 m2 : cm_Mode,
    cm_minDistComp m1 m2 = cm_minDistComp m2 m1;
  cm_maxMinDistComp : cm_Mode -> Distance;
  cm_maxMinDistCompBound : forall m m' : cm_Mode,
    cm_minDistComp m m' <= cm_maxMinDistComp m;
  cm_minDistCompFS : forall m1 m2 : cm_Mode,
    cm_failSafe m1 -> cm_minDistComp m1 m2 = mkDistance zeroNonneg;
  cm_period : cm_Mode -> Time;
  cm_msgLatency_positive : 0 < cm_msgLatency;
  cm_period_positive : forall m : cm_Mode, 0 < cm_period m;
  cm_speedMax_pos : 0 < cm_speedMax;
  cm_adaptNotif_positive : 0 < cm_adaptNotif;
  cm_modeTransTime_bound : forall (m mF : cm_Mode) (p : cm_modeTransRel m mF),
    cm_failSafe mF -> cm_modeTransTime m mF p <= cm_trans m
}.

(** The global axioms form a [ComhModel]: the record captures exactly them. *)
Definition global_model : ComhModel := {|
  cm_adaptNotif := adaptNotif;
  cm_msgLatency := msgLatency;
  cm_speedMax := speedMax;
  cm_Mode := Mode;
  cm_failSafe := failSafe;
  cm_fsDecMode := fsDecMode;
  cm_eqDecMode := eqDecMode;
  cm_modeTransRel := modeTransRel;
  cm_modeTransRelDec := modeTransRelDec;
  cm_modeTransTime := modeTransTime;
  cm_failSafeSucc := failSafeSucc;
  cm_failSafeSuccFS := failSafeSuccFS;
  cm_failSafeSucc_successor := failSafeSucc_successor;
  cm_trans := trans;
  cm_transMax := transMax;
  cm_waitSurplus := waitSurplus;
  cm_transMaxBound := transMaxBound;
  cm_minDistComp := minDistComp;
  cm_minDistCompSymmetric := minDistCompSymmetric;
  cm_maxMinDistComp := maxMinDistComp;
  cm_maxMinDistCompBound := maxMinDistCompBound;
  cm_minDistCompFS := minDistCompFS;
  cm_period := period;
  cm_msgLatency_positive := msgLatency_positive;
  cm_period_positive := period_positive;
  cm_speedMax_pos := speedMax_pos;
  cm_adaptNotif_positive := adaptNotif_positive;
  cm_modeTransTime_bound := modeTransTime_bound
|}.

(** ** A concrete, non-degenerate model *)

Inductive CMode : Type := Safe | Moving.

Definition cFailSafe (m : CMode) : Prop := m = Safe.

Definition oneNonneg : nonnegreal := mknonnegreal 1 Rle_0_1.
Definition oneTime : Time := mkTime oneNonneg.
Definition oneDelay : Delay := mkDelay (mkposreal 1 Rlt_0_1).
Definition oneDistance : Distance := mkDistance oneNonneg.
Definition zeroDistance : Distance := mkDistance zeroNonneg.

(** Only two [Moving] entities need to keep apart (by distance 1). *)
Definition cMinDistComp (m1 m2 : CMode) : Distance :=
  match m1, m2 with
  | Moving, Moving => oneDistance
  | _, _ => zeroDistance
  end.

Definition cMaxMinDistComp (m : CMode) : Distance :=
  match m with
  | Moving => oneDistance
  | Safe => zeroDistance
  end.

Lemma cFsDec : forall m : CMode, decidable (cFailSafe m).
Proof.
  intros []; unfold decidable, cFailSafe; [left | right]; congruence.
Qed.

Lemma cEqDec : eqDec CMode.
Proof. unfold eqDec. decide equality. Qed.

Lemma cTransDec : forall m1 m2 : CMode, {True} + {~ True}.
Proof. left. exact I. Qed.

Definition concrete_model : ComhModel := {|
  cm_adaptNotif := oneTime;
  cm_msgLatency := oneTime;
  cm_speedMax := oneNonneg;
  cm_Mode := CMode;
  cm_failSafe := cFailSafe;
  cm_fsDecMode := cFsDec;
  cm_eqDecMode := cEqDec;
  cm_modeTransRel := fun _ _ => True;
  cm_modeTransRelDec := cTransDec;
  cm_modeTransTime := fun _ _ _ => oneTime;
  cm_failSafeSucc := fun _ => Safe;
  cm_failSafeSuccFS := fun _ => eq_refl;
  cm_failSafeSucc_successor := fun _ => I;
  cm_trans := fun _ => oneTime;
  cm_transMax := oneTime;
  cm_waitSurplus := oneDelay;
  cm_transMaxBound := fun _ => Rle_refl 1;
  cm_minDistComp := cMinDistComp;
  cm_minDistCompSymmetric := ltac:(intros [] []; reflexivity);
  cm_maxMinDistComp := cMaxMinDistComp;
  cm_maxMinDistCompBound := ltac:(intros [] []; simpl; lra);
  cm_minDistCompFS := ltac:(intros m1 m2 H; unfold cFailSafe in H; subst; destruct m2; reflexivity);
  cm_period := fun _ => oneTime;
  cm_msgLatency_positive := Rlt_0_1;
  cm_period_positive := fun _ => Rlt_0_1;
  cm_speedMax_pos := Rlt_0_1;
  cm_adaptNotif_positive := Rlt_0_1;
  cm_modeTransTime_bound := fun _ _ _ _ => Rle_refl 1
|}.

(** The model really is non-degenerate. *)
Lemma concrete_model_nondegenerate :
  ~ cm_failSafe concrete_model Moving /\
  0 < cm_minDistComp concrete_model Moving Moving.
Proof. simpl. unfold cFailSafe. split; [discriminate | lra]. Qed.

(** Expected: no [ComhBasics] axiom, only stdlib real-number axioms. *)
Print Assumptions concrete_model.
Print Assumptions concrete_model_nondegenerate.
