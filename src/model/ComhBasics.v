(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** The Comhordú model, as a class whose fields are the constants that any system using the
protocol supplies, and some basic notions defined from them, such as when a coverage is
sufficient for a mode.*)

Require Import ComhCoq.lib.Extras.LibTactics.
From Stdlib Require Import Reals Arith Lia.
Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.

(*********Comh Related Stuff********)

Open Scope R_scope.

(** The Comhordú model of the thesis (§3.3, p.41): the parameters that any system using the
protocol supplies, and the constraints they must meet. Every result about the protocol
holds for every instance.*)
Class ComhModel := {
  (** The time it takes for an entity to be notified of a message delivery area.*)
  adaptNotif : Time;
  (** The time between initiating the sending of a message and its actual delivery.*)
  msgLatency : Time;
  (**We assume a maximum speed at which entities may travel.*)
  speedMax : nonnegreal;
  (** The set of all modes.*)
  Mode : Type;
  (** A subset of the modes are fail safe.*)
  failSafe : Mode -> Prop;
  (** A mode is either fail safe or it isn't.*)
  fsDecMode : forall (m : Mode), decidable (failSafe m);
  (** Equality on modes is decidable.*)
  eqDecMode : eqDec Mode;
  (** The mode transition relation, which says whether one mode can transition
  to another or not.*)
  modeTransRel : Mode -> Mode -> Prop;
  (** The mode transition relation is assumed to be decidable.*)
  modeTransRelDec : forall (m1 m2 : Mode),
    {modeTransRel m1 m2} + {~modeTransRel m1 m2};
  (** modeTransTime m1 m2 gives the time it takes to transition from
  m1 to m2. Note that this function takes two modes and a proof that one
  transitions to the other and then returns the transition time.*)
  modeTransTime : forall (m1 m2 : Mode), modeTransRel m1 m2 -> Time;
  (** We assume that every mode transitions to some fail safe mode,
  and this function simply arbitrarily picks one such fail safe mode.*)
  failSafeSucc : Mode -> Mode;
  (** This is the assumption that failSafeSucc m is indeed fail safe for all m.*)
  failSafeSuccFS : forall (m : Mode), failSafe (failSafeSucc m);
  (*The fail safe successor is actually a successor.*)
  failSafeSucc_successor : forall m, modeTransRel m (failSafeSucc m);
  (** trans m is the worst case time it takes for an entity in a mode m
  to reach a failsafe mode.*)
  trans : Mode -> Time;
  (** An upper bound on trans m over all m: transMax is an upper bound on
  the time it takes any entity to reach a failsafe mode.*)
  transMax : Time;
  (**A little extra positive time that ensures we wait beyond the boundary*)
  waitSurplus : Delay;
  (** transMax is an upper bound on trans m for all m.*)
  transMaxBound : forall m : Mode, trans m <= transMax;
  (** The minimum distance of compatibiltiy function is assumed to exist.
  It tells us the minimum distance by which two modes must be separated in
  order for them to be compatible. If two entities in these modes are
  separated by a distance greater than or equal to this distance,
  then they are compatible.*)
  minDistComp : Mode -> Mode -> Distance;
  (** The minimum distance of compatibility function is symmetric.*)
  minDistCompSymmetric : forall (m1 m2 : Mode), minDistComp m1 m2 = minDistComp m2 m1;
  (** For a given mode m, maxMinDistComp m is an upper bound on the set
  minDistComp m m' taken over all other modes m'. We do not enforce that this
  is the least such upper bound, though this would be the sensible interpretation.*)
  maxMinDistComp : Mode -> Distance;
  (** The maxMinDistComp is an upper bound on the minDistComp for all other modes*)
  maxMinDistCompBound : forall m m' : Mode, minDistComp m m' <= maxMinDistComp m;
  (** The minimum distance of compatibility function returns 0 if either
  of its arguments are fail safe. Note we only choose the left argument here,
  but the choice is irrelevant since the function is symmetric.*)
  minDistCompFS : forall (m1 m2 : Mode),
    failSafe m1 -> minDistComp m1 m2 = (mkDistance zeroNonneg);
  (** period m is the time between successive broadcasts from an entity in mode m.*)
  period : Mode -> Time;
  msgLatency_positive : 0 < msgLatency;
  period_positive : forall m : Mode, 0 < period m;
  (** To rule out a trivial system, we assume the maximum speed is above 0.*)
  speedMax_pos : 0 < speedMax;
  adaptNotif_positive : 0 < adaptNotif;
  (** trans m bounds the time to transition from m to any fail-safe successor
  (Definition 5.2, p.107).*)
  modeTransTime_bound : forall (m mF : Mode) (p : modeTransRel m mF),
    failSafe mF -> modeTransTime m mF p <= trans m }.

Notation "m1 -mtr-> m2" := (modeTransRel m1 m2) (at level 39).

Section ComhBasics.
Context {Model : ComhModel}.

(** Mode transition relation as a boolean function.*)
Definition modeTransRelBool (m1 m2 : Mode) : bool :=
  decToBool (modeTransRelDec m1 m2).

(** Mode transition relation as an option type*)
Definition modeTransRelOpt (m1 m2 : Mode) : option (m1 -mtr-> m2) :=
  decToOption (modeTransRelDec m1 m2).

(** The wait time between two modes m1 and m2 is the maximum between two different
values. The first is the mode transition time, denoting the physical time it takes
to transition from one mode to another. The second value ensures that the wait time
is to sufficient to ensure surrounding entities are warned. As such, it incorporates
the term msgLatency to allow the initial message to be delivered, transMax for the
receiving entities to react, adaptNotif for the sender to be notified of the coverage,
and finally some positive waitSurplus to ensure that the message delivery, reaction and
notification have definitely happened in the past- without the surplus it might be possible
for these events to be about to happen this instant but they might not have happened yet.*)
Definition waitTime (m1 m2 : Mode) (p : m1 -mtr-> m2) : Time :=
  timeMax (modeTransTime m1 m2 p)
  (msgLatency +t+ (timeMax adaptNotif transMax) +t+ waitSurplus).

Lemma speedMax_nonneg : 0 <= speedMax.
Proof.
  (*Proof: follows from speedMax_pos*)
  apply Rlt_le. apply speedMax_pos.
Qed.

(** The coverage r is sufficient for an entity broadcasting in mode m.*)
Definition sufficient (m : Mode) (r : Distance) : Prop :=
  maxMinDistComp m +
  2 * speedMax * (Rmax adaptNotif transMax + period m + trans m) <= r.

(** The sufficient predicate is decidable.*)
Lemma suffDec : forall (m : Mode) (r : Distance),
  {sufficient m r} + {~sufficient m r}.
Proof. intros. apply Rle_dec. Qed.

(** A version of the sufficient Prop that gives a bool as a result.*)
Definition suffBool (m : Mode) (r : Distance) : bool :=
  if suffDec m r then true else false.

(** The possibly incompatible distance for modes m and m' is the distance
beneath which an entity in mode m must consider mode m' messages from other entities
as potential threats.*)
Definition possIncDist (m m' : Mode) : R :=
  minDistComp m m' + 2 * speedMax * (Rmax adaptNotif transMax + period m' + trans m').

(** possiblyIncompatible m m' r means that if e and e' in m and m'
respectively are separated by r, then e' should begin to transition to a
fail safe mode if it has not already done so.*)
Definition possiblyIncompatible (m m' : Mode) (r : R) :=
  r < possIncDist m m'.

Lemma possIncDec : forall (m m' : Mode) (r : Distance),
  {possiblyIncompatible m m' r} + {~possiblyIncompatible m m' r}.
Proof.
  intros.
  apply Rlt_dec.
Qed.

(** A version of the possiblyIncompatible Prop that gives a bool as a result.*)
Definition possIncBool (m m' : Mode) (r : Distance) : bool :=
  if possIncDec m m' r then true else false.


(** If m m' r are possibly incompatible, r' is a sufficient coverage for m, then
r <= r'.*)
Theorem possIncSuff : forall (m m' : Mode) (r r' : Distance),
  possiblyIncompatible m m' r -> sufficient m' r' -> r < r'.
Proof.
  unfold possiblyIncompatible, sufficient. intros.
  eapply Rlt_le_trans. apply H. eapply Rle_trans; try apply H0.
  apply Rplus_le_compat. rewrite minDistCompSymmetric.
  apply maxMinDistCompBound. apply Rle_refl.
Qed.

(** This is the interval in the past during which we show that any entity
in a non fail safe mode m must have sent a message containing mode m.*)
Definition preSentInterval (m : Mode) : Interval :=
  let lower := msgLatency + Rmax adaptNotif transMax in
  let upper := lower + period m + trans m in
  (\lower, upper\].

(** The interval of time in the past during which we can show a
sufficient pre-broadcast takes place, parametrised on the mode m.*)
Definition preDeliveredInterval (m : Mode) : Interval :=
  let lower := Rmax adaptNotif transMax in
  let upper := lower + period m + trans m in
  (\lower, upper\].



(** The upper bound of the pre bc suff interval is positive*)
Lemma preBcSuffUpperPos : forall m : Mode,
  0 <= upper (preDeliveredInterval m).
Proof.
  intros. apply Rle_trans with (r2 := adaptNotif).
  destruct adaptNotif. destruct time. apply cond_nonneg.
  replace (nonneg (time adaptNotif)) with
  (nonneg (time adaptNotif) + 0 + 0). 
  unfold preDeliveredInterval. simpl. repeat apply Rplus_le_compat.
  apply Rmax_l. destruct (period m). destruct time. apply cond_nonneg.
  destruct (trans m). destruct time. apply cond_nonneg.
  ring.
Qed.

(*2*speedMax gets used a lot, as it is the maximum relative speed, so we prove this special
result for it*)
Lemma speedMax_double_nonneg : 0 <= 2*speedMax.
Proof.
  replace 0 with (2*0).
  apply Rmult_le_compat_l. apply two_nonneg. apply speedMax_nonneg.
  ring.
Qed.

(**All numbers within the preDeliveredInterval are strictly positive.*)
Lemma inPreBcSuffPos : forall (m : Mode) (u : Time),
  u [:] (preDeliveredInterval m) -> 0 < u.
Proof.
  intros. inversion H.
  simpl in H0. apply Rle_lt_trans with (r2 := adaptNotif).
  timeNonneg. eapply Rle_lt_trans; try apply H0.
  apply Rmax_l.
Qed.

(*LOCAL TIDY*)

Lemma sufficient_suffBool m r : sufficient m r ->
  suffBool m r = true.
Proof.
  intros. unfold suffBool.
  remember (suffDec m r) as SD. destruct SD. reflexivity.
  false.
Qed.

Lemma possInc_possIncBool m m' r :
  possiblyIncompatible m m' (distance r) ->
  possIncBool m m' r = true.
Proof.
  intros. unfold possIncBool.
  remember (possIncDec m m' r) as PD. destruct PD. reflexivity.
  false.
Qed.

Lemma possIncBool_possInc m m' r :
  possIncBool m m' r = true ->
  possiblyIncompatible m m' (distance r).
Proof.
  unfold possIncBool. intros. remember (possIncDec m m' r) as PD.
  destruct PD. assumption. inversion H.
Qed.

Lemma possIncDist_positive m1 m2 : 0 < possIncDist m1 m2.
Proof.
  (*Proof: follows from adaptNotif_positive and speedMax_pos.*)
  replace 0 with (0 + 0); [ | ring]. apply Rplus_le_lt_compat.
  apply cond_nonneg. repeat(apply Rmult_lt_0_compat ||
  apply Rlt_0_1 || apply Rlt_R0_R2). apply speedMax_pos.
  apply Rlt_le_trans with (r2 := adaptNotif). apply adaptNotif_positive.
  rewrite <- Rplus_0_r at 1. rewrite <- Rplus_0_r at 1.
  repeat (apply Rplus_le_compat); try timeNonneg.
  apply Rmax_l.
Qed.

End ComhBasics.
