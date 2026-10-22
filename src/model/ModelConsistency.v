(** * The model's assumptions are consistent

    [safety] holds for every model: every instance of the class [ComhModel] of
    [ComhBasics]. That would mean nothing if there were no model, or only degenerate
    ones. [concrete_model] is a model built without axioms:
    [Print Assumptions concrete_model] shows only the standard library's axioms for
    the reals. It is deliberately non-degenerate:
    - It has two modes: [Safe], which is fail-safe, and [Moving], which is not.
    - Every transition is permitted.
    - Two [Moving] entities must keep a positive distance (1) apart.

    So safety is a real constraint in this model, not something every
    configuration satisfies trivially.

    [concrete_model] is not declared as an instance of the class, so Rocq never
    supplies it where a result is meant to hold for every model. *)

From Stdlib Require Import Reals Lra.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.

Open Scope R_scope.

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
  adaptNotif := oneTime;
  msgLatency := oneTime;
  speedMax := oneNonneg;
  Mode := CMode;
  failSafe := cFailSafe;
  fsDecMode := cFsDec;
  eqDecMode := cEqDec;
  modeTransRel := fun _ _ => True;
  modeTransRelDec := cTransDec;
  modeTransTime := fun _ _ _ => oneTime;
  failSafeSucc := fun _ => Safe;
  failSafeSuccFS := fun _ => eq_refl;
  failSafeSucc_successor := fun _ => I;
  trans := fun _ => oneTime;
  transMax := oneTime;
  waitSurplus := oneDelay;
  transMaxBound := fun _ => Rle_refl 1;
  minDistComp := cMinDistComp;
  minDistCompSymmetric := ltac:(intros [] []; reflexivity);
  maxMinDistComp := cMaxMinDistComp;
  maxMinDistCompBound := ltac:(intros [] []; simpl; lra);
  minDistCompFS := ltac:(intros m1 m2 H; unfold cFailSafe in H; subst; destruct m2; reflexivity);
  period := fun _ => oneTime;
  msgLatency_positive := Rlt_0_1;
  period_positive := fun _ => Rlt_0_1;
  speedMax_pos := Rlt_0_1;
  adaptNotif_positive := Rlt_0_1;
  modeTransTime_bound := fun _ _ _ _ => Rle_refl 1
|}.

(** The model really is non-degenerate. *)
Lemma concrete_model_nondegenerate :
  ~ @failSafe concrete_model Moving /\
  0 < @minDistComp concrete_model Moving Moving.
Proof. simpl. unfold cFailSafe. split; [discriminate | lra]. Qed.

(** Expected: only the standard library's axioms for the reals. *)
Print Assumptions concrete_model.
Print Assumptions concrete_model_nondegenerate.
