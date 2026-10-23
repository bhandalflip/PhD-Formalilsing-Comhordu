(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** Theorems about Real numbers, distances, intervals.*)

(***************************** Standard Imports *****************************)
Require Import ComhCoq.lib.Extras.LibTactics.
From Stdlib Require Export Reals Arith.
From Stdlib Require Export Logic.ProofIrrelevance.
Require Import ComhCoq.lib.GenTacs.
Require Export ComhCoq.lib.RInequalities.
From Stdlib Require Import Lra.

Open Scope R_scope.

(****************************** Misc ******************************)

(**Equality is decidable on the set X.*)
Definition eqDec (X : Type) := forall x1 x2 : X,
  {x1 = x2} + {x1 <> x2}.

Lemma notEq_symm : forall (X : Type) (x1 x2 : X), ~x1 = x2 -> ~x2 = x1.
Proof. unfold not. intros. apply H. symmetry. assumption. Qed.

Lemma two_nonneg : 0 <= 2.
Proof. lra. Qed.
  
Ltac Rplus3_swap_2_3 a b c := replace (a + b + c) with (a + c + b); [ | ring].
Ltac Rminus_plus_zero a b := replace (a - b) with (a + (0 - b));[ | ring].

(****************************** Restricted Reals ******************************)

(** Performs a contradiction on the assumption that some non-negative real is
less than 0, i.e. negative.*)
Ltac nonneg_lt0_contra :=
  match goal with
  | [H : (nonneg ?x) < 0 |- _] =>
    apply Rlt_not_le in H; false; apply H; unwrap_apply2 x
  end.

(** The number one as a positive real number.*)
Definition onePos : posreal.
Proof.
  assert (0 < (INR 1)). apply lt_0_INR.
  constructor. eapply mkposreal. apply H.
Defined.

Definition zeroNonneg : nonnegreal := mknonnegreal 0 (Rle_refl 0).

(** Euclidean distance is always >= 0.*)
Lemma dist_euc_nonneg : forall (x1 y1 x2 y2 : R),
  0 <= dist_euc x1 y1 x2 y2.
Proof.
  intros. unfold dist_euc.
  apply sqrt_positivity. apply Rplus_le_le_0_compat;
  apply Rle_0_sqr.
Qed.

(** Adding a vector to both points leaves distance unchanged.*)
Lemma dist_eucAddPres : forall (x1 y1 x2 y2 x3 y3 : R),
  dist_euc x1 y1 x2 y2 = dist_euc (x1 + x3) (y1 + y3) (x2 + x3) (y2 + y3).
Proof. intros. unfold dist_euc. unfold Rsqr. f_equal. ring. Qed.

(** Adding (x, y) to one of the coordinates of dist_euc yeilds and expression
that is within |(x, y)| of the original.*)
Lemma dist_eucAddLe : forall (x1 y1 x2 y2 x3 y3 : R),
  dist_euc (x1 + x3) (y1 + y3) (x2) (y2) <=
  dist_euc x1 y1 x2 y2 + dist_euc x3 y3 0 0.
Proof.
  intros. rewrite (dist_eucAddPres x3 y3 0 0 x1 y1).
  repeat rewrite Rplus_0_l. rewrite Rplus_comm.
  replace (dist_euc x1 y1 x2 y2 + dist_euc (x3 + x1) (y3 + y1) x1 y1)
  with (dist_euc (x3 + x1) (y3 + y1) x1 y1 + dist_euc x1 y1 x2 y2).
  replace (y3 + y1) with (y1 + y3). apply triangle. apply Rplus_comm.
  apply Rplus_comm.
Qed.

(**To show the equality of two nonnegative reals, it suffices to show
the equality of the numerical parts, i.e. we can ignore the proof terms.*)
Lemma nonnegRealEqR : forall (r1 r2 : nonnegreal),
  nonneg r1 = nonneg r2 -> r1 = r2.
Proof.
  intros. destruct r1. destruct r2.
  simpl in H. generalize cond_nonneg. rewrite H. intros. f_equal.
  apply proof_irrelevance.
Qed.

(**To show the equality of two positive reals, it suffices to show
the equality of the numerical parts, i.e. we can ignore the proof terms.*)
Lemma posRealEqR : forall (r1 r2 : posreal),
  pos r1 = pos r2 -> r1 = r2.
Proof.
  intros. destruct r1. destruct r2.
  simpl in H. generalize cond_pos. rewrite H. intros. f_equal.
  apply proof_irrelevance.
Qed.

Open Scope R_scope.

(** Multiplication defined for nonneg reals.*)
Definition multNonneg (r1 r2 : nonnegreal) : nonnegreal :=
  let prod := (r1 * r2) in
  let h1 := cond_nonneg r1 in
  let h2 := cond_nonneg r2 in
  let h := Rmult_le_0_compat r1 r2 h1 h2 in
  mknonnegreal prod h.
Notation "r1 *nn* r2" := (multNonneg r1 r2) (at level 40, left associativity).

(** Subtraction on nonnegative reals as a total function.
Gives r1 - r2 if that result is nonnegative, else returns 0.*)
Definition subNonnegTot (r1 r2 : nonnegreal) : nonnegreal :=
  match (Rle_dec r2 r1) with
  | left p => mknonnegreal (r1 - r2) (RleMinusBothSides r1 r2 p)
  | _ => zeroNonneg
  end.
Notation "r1 -nn- r2" := (subNonnegTot r1 r2) (at level 50).

(** Adds two nonnegreals together to get a resulting nonegreal.*)
Definition addNonneg (r1 r2 : nonnegreal) : nonnegreal :=
  match r1 with
  | {|nonneg := x1; cond_nonneg := cn1 |} => match r2 with
  | {|nonneg := x2; cond_nonneg := cn2 |} => let r := x1 + x2 in
  let Heqr := eq_refl r in
  {| nonneg := r; cond_nonneg := eq_ind_r (fun r0 : R => 0 <= r0)
   (Rplus_le_le_0_compat x1 x2 cn1 cn2) Heqr |} end end.
Notation "x +nn+ y" := (addNonneg x y) (at level 50).

(** Adding two nonneg numbers and then removing the real part is the same
as removing the real part and then adding*)
Lemma addNonnegFact : forall (r1 r2 : nonnegreal),
  nonneg (r1 +nn+ r2) = (nonneg r1) + (nonneg r2).
Proof.
  intros. unfold addNonneg. destruct r1, r2. simpl.
  reflexivity.
Qed.

(** zeroNonneg is the right zero for addNonneg*)
Lemma addNonnegZeroR : forall (r : nonnegreal),
  r +nn+ zeroNonneg = r.
Proof. intro r. apply nonnegRealEqR. rewrite addNonnegFact. simpl. ring. Qed.

(** zeroNonneg is the right zero for addNonneg*)
Lemma addNonnegZeroL : forall (r : nonnegreal),
  zeroNonneg +nn+ r = r.
Proof. intro r. apply nonnegRealEqR. rewrite addNonnegFact. simpl. ring. Qed.

(** Addition of nonnegative reals is associative*)
Lemma addNonnegAssoc : forall (r1 r2 r3 : nonnegreal),
  r1 +nn+ (r2 +nn+ r3) = r1 +nn+ r2 +nn+ r3.
Proof.
  intros. apply nonnegRealEqR.
  repeat (rewrite addNonnegFact). ring.
Qed.

Lemma addNonnegComm : forall (r1 r2 : nonnegreal),
  r1 +nn+ r2 = r2 +nn+ r1.
Proof.
  intros. destruct r1, r2.
  simpl. apply nonnegRealEqR. simpl. ring.
Qed.

Lemma addNonnegCancel : forall (r1 r2 r3 : nonnegreal),
  r1 +nn+ r2 = r1 +nn+ r3 -> r2 = r3.
Proof.
  intros r1 r2 r3 H. apply nonnegRealEqR. apply (f_equal nonneg) in H.
  rewrite !addNonnegFact in H. lra.
Qed.

(**Equality is decidable for reals.*)
Lemma eqDecReal : eqDec R.
Proof.
  unfold eqDec. intros.
  generalize (total_order_T x1 x2). intros.
  inversion H. inversion H0. right. unfold not; intros. apply Rlt_not_eq in H1.
  inversion H2. apply H1. assumption. left. f_equal. assumption. right. unfold not.
  intros. apply Rlt_not_eq in H0. apply H0. symmetry.  assumption.
Qed.

Lemma eqDecNonnegReal : eqDec nonnegreal.
Proof.
  unfold eqDec. destruct x1, x2.
  generalize (eqDecReal nonneg nonneg0).
  intros. inversion H. left. generalize dependent cond_nonneg.
  generalize dependent cond_nonneg0. rewrite H0. intros. repeat f_equal.
  apply proof_irrelevance. right. unfold not; intros. inversion H1.
  apply H0. assumption.
Qed.

Lemma eqDecPosReal : eqDec posreal.
Proof.
  unfold eqDec. destruct x1, x2.
  generalize (eqDecReal pos pos0).
  intros. inversion H. left. generalize dependent cond_pos.
  generalize dependent cond_pos0. rewrite H0. intros. repeat f_equal.
  apply proof_irrelevance. right. unfold not; intros. inversion H1.
  apply H0. assumption.
Qed.

(** Coerce a positive real to a nonnegative real.*)
Coercion posToNonneg (r : posreal) : nonnegreal :=
  match r with mkposreal p c =>
    mknonnegreal p (Rlt_le 0 p c) end.

(** Every positive real is the sum of two positive reals. The simplest
existential witnesses for this are both half the original number i.e. every number is equal
to half itself plus half itself.*)
Theorem addPosRealExists : forall (r : posreal),
  exists r1 r2, pos r = pos r1 + pos r2.
Proof.
  intros. assert (H : 0 < r/2) by (pose proof (cond_pos r); lra).
  exists (mkposreal _ H) (mkposreal _ H). simpl. lra.
Qed.




(****************************** Position ******************************)

(** A position is a pair of reals.*)
Record Position := mkPosition {xCoord : R; yCoord : R}.

(** Addition on positions (vector addition).*)
Definition addPos (p1 p2 : Position) : Position :=
  let x1 := xCoord p1 in let y1 := yCoord p1 in
  let x2 := xCoord p2 in let y2 := yCoord p2 in
  mkPosition (x1 + x2) (y1 + y2).
Notation "p1 +p+ p2" := (addPos p1 p2) (at level 50).
Hint Unfold addPos.

(** Subtraction (vector) on positions.*)
Definition minusPos (p1 p2 : Position) : Position :=
  let x1 := xCoord p1 in let y1 := yCoord p1 in
  let x2 := xCoord p2 in let y2 := yCoord p2 in
  mkPosition (x1 - x2) (y1 - y2).
Notation "p1 -~p- p2" := (minusPos p1 p2) (at level 50).
Hint Unfold minusPos.

Definition oppPos (p : Position) : Position :=
  let x := xCoord p in let y := yCoord p in
  mkPosition (-x) (-y).
Notation "~- p" := (oppPos p) (at level 40).
Hint Unfold oppPos.

(** The Euclidean distance between a pair of positions.*)
Definition dist2d (p1 p2 : Position) : nonnegreal :=
  mknonnegreal
  (dist_euc (xCoord p1) (yCoord p1) (xCoord p2) (yCoord p2))
  (dist_euc_nonneg (xCoord p1) (yCoord p1) (xCoord p2) (yCoord p2)).

(** The origin is the point (0, 0).*)
Definition origin := mkPosition 0 0.

(** The vector length of a position. Defined to be the distance between
that position and (0, 0).*)
Definition displacement (p : Position) : nonnegreal := dist2d p origin.

Ltac unfoldPosDefs := unfold addPos; unfold minusPos; unfold oppPos;
  unfold dist; unfold origin; unfold displacement.

(** The negation of p1 - p2 is p2 - p1.*)
Theorem oppMinusPos : forall (p1 p2 : Position),
   ~-(p1 -~p- p2) = (p2 -~p- p1).
Proof. intros. unfoldPosDefs. f_equal; simpl; ring. Qed.

(** 0 is the right unit of plus.*)
Theorem plusRightUnitPos : forall (p1 : Position),
  p1 +p+ origin = p1.
Proof.
  intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring.
Qed.

(** 0 is the left unit of plus.*)
Theorem plusLeftUnitPos : forall (p1 : Position),
  origin +p+ p1 = p1.
Proof.
  intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring.
Qed.

Theorem minusCancellativePos : forall (p1 : Position),
  p1 -~p- p1 = origin.
Proof. intros. unfoldPosDefs. f_equal; ring. Qed.

(** Subtracting p2 is that same as adding -p2.*)
Theorem minusPlusOppPos : forall (p1 p2 : Position),
  p1 -~p- p2 = p1 +p+ (~-p2).
Proof. intros. unfoldPosDefs. f_equal. Qed.

(** Add and then subtract p2 and you're left with the original position.*)
Lemma plusMinusCancelPos : forall (p1 p2 : Position),
  p1 +p+ p2 -~p- p2 = p1.
Proof.
  intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring.
Qed.

(** Subtract and then add p2 and you're left with the original position.*)
Lemma minusPlusCancelPos : forall (p1 p2 : Position),
  p1 -~p- p2 +p+ p2 = p1.
Proof.
  intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring.
Qed.

(** The distance function is symmetric.*)
Lemma distSymmetric : forall (p1 p2 : Position), dist2d p1 p2 = dist2d p2 p1.
Proof.
  intros. unfold dist2d. f_equal. apply nonnegRealEqR. simpl.
  apply distance_symm.
Qed.

(** Adding the difference between two vectors to the subtracted
vector gets you the other vector.*)
Theorem minusPlusInvPos : forall (p1 p2 : Position),
  p1 = p2 +p+ (p1 -~p- p2).
Proof.
  intros. destruct p1. unfoldPosDefs. simpl.
  repeat rewrite Rplus_minus. reflexivity.
Qed.

(** Adding the same vector to the arguments of dist2d preserves the result.*)
Theorem distAddPres : forall (p1 p2 p3 : Position),
  dist2d p1 p2 = dist2d (p1 +p+ p3) (p2 +p+ p3).
Proof.
  intros.
  unfold dist2d. destruct p1, p2, p3. simpl.
  generalize (dist_euc_nonneg xCoord0 yCoord0 xCoord1 yCoord1).
  generalize (dist_euc_nonneg (xCoord0 + xCoord2) (yCoord0 + yCoord2)
                 (xCoord1 + xCoord2) (yCoord1 + yCoord2)).
  rewrite <- dist_eucAddPres with (x3 := xCoord2) (y3 := yCoord2).
  intros. f_equal. apply proof_irrelevance.
Qed.

(** Subtracting the same vector to the arguments of dist2d preserves the result.*)
Theorem distMinusPres : forall (p1 p2 p3 : Position),
  dist2d p1 p2 = dist2d (p1 -~p- p3) (p2 -~p- p3).
Proof.
  intros.
  repeat rewrite minusPlusOppPos. apply distAddPres.
Qed.

(** The distance between p1 and p2 is the same as the length of p1 - p2.*)
Theorem minusLengthDistance : forall (p1 p2 : Position),
  dist2d p1 p2 = displacement (p1 -~p- p2).
Proof.
  intros. unfold displacement.
  rewrite (distAddPres (p1 -~p- p2) origin p2). rewrite minusPlusCancelPos.
  f_equal. rewrite plusLeftUnitPos. reflexivity.
Qed.

(** Adding p3 to p1 changes the distance between p1 and p2 by
at most |p3|.*)
Theorem distAddLe : forall (p1 p2 p3 : Position),
  dist2d (p1 +p+ p3) (p2) <= dist2d p1 p2 + displacement p3.
Proof.
  intros.
  destruct p1, p2, p3. unfoldPosDefs. simpl. apply dist_eucAddLe.
Qed.

(** Adding p3 to p1 changes the distance between p1 and p2 by
at most r if |p3| <= r.*)
Theorem distAddLeLe : forall (p1 p2 p3 : Position) (r : R),
  displacement p3 <= r -> dist2d (p1 +p+ p3) (p2) <= dist2d p1 p2 + r.
Proof.
  intros.
  pose proof (distAddLe p1 p2 p3). lra.
Qed.

(** If the distance between p1 and p1' is bounded above by r, and the
same holds for p2 and p2', then the distance between p1 and p2 is
at most the difference between p1' and p2' + 2r.*)
Theorem posDiffBound : forall (p1 p2 p1' p2' : Position) (r : R),
  dist2d p1  p1' <= r -> dist2d p2 p2' <= r ->
  dist2d p1 p2 <= dist2d p1' p2' + 2*r.
Proof.
  intros. assert (2*r = r + r).
  ring. rewrite H1. rewrite <- Rplus_assoc.
  eapply Rle_trans. rewrite (minusPlusInvPos p1 p1'). apply distAddLeLe.
  rewrite <- minusLengthDistance. apply H. rewrite (minusPlusInvPos p2 p2').
  apply Rplus_le_compat_r. rewrite distSymmetric.
  replace (dist2d p1' p2') with (dist2d p2' p1'); try apply distSymmetric.
  apply distAddLeLe. rewrite <- minusLengthDistance. apply H0.
Qed.

Lemma eqDecPosition : eqDec Position.
Proof.
  unfold eqDec.
  destruct x1, x2. generalize (eqDecReal xCoord0 xCoord1).
  generalize (eqDecReal yCoord0 yCoord1). intros.
  inversion H. inversion H0. left. f_equal; assumption.
  right. unfold not; intros. apply H2. inversion H3.
  reflexivity. right. unfold not; intros. apply H1. inversion H2.
  reflexivity.
Qed.

Lemma dist_tri_ineq : forall (l1 l2 l3 : Position),
  dist2d l1 l3 <= dist2d l1 l2 + dist2d l2 l3.
Proof.
  intros l1 l2 l3. apply triangle.
Qed.

Lemma dist2D_refl : forall l : Position, dist2d l l = zeroNonneg.
Proof.
  intros.
  apply nonnegRealEqR. unfold dist2d. simpl. apply distance_refl.
Qed.

(****************************** Interval ******************************)

(** An interval on the real line. We allow upper < lower, the interpretation
in this case being that the interval is empty. The two fields lowerClosed and
upperClosed allow for the four possibilities of interval, from fully closed
to fully open: [], [), (], ().*)
Record Interval := mkInterval{
  lower : R;
  upper : R;
  lowerClosed : bool;
  upperClosed : bool
  }.

(** inInterval r i means that the real number r is in the Interval i,
where i is interpreted as a closed interval.*)
Definition inInterval (r : R) (i : Interval) :=
  match lowerClosed i, upperClosed i with
  | true, true => lower i <= r <= upper i
  | true, false => lower i <= r < upper i
  | false, true => lower i < r <= upper i
  | false, false => lower i < r < upper i
  end.
Notation "r [:] i" := (inInterval r i) (at level 70).

(** v1 is a (non-strict) sub interval of v2*)
Definition subInterval (i1 i2 : Interval) : Prop :=
  forall r : R, r [:] i1 -> r [:] i2.

Open Scope R_scope.

(** Add the lower bounds and the upper bounds just as in vector addition.
Closedness of a bound in the resulting interval is equivalent to closedness of
the respective bounds in both i1 and i2.*)
Definition addInterval (i1 i2 : Interval) : Interval :=
  match i1 with (mkInterval l1 u1 lc1 uc1) =>
  match i2 with (mkInterval l2 u2 lc2 uc2) =>
  mkInterval (l1 + l2) (u1 + u2) (andb lc1 lc2) (andb uc1 uc2)
  end end.
Notation "i [++] i'" := (addInterval i i') (at level 45).

(** If x is in i then x is less than or equal to the upper bound of i.*) 
Lemma inIntervalLeUpper : forall (i : Interval) (x : R),
  x [:] i -> x <= upper i.
Proof. intros [l u [|] [|]] x H; unfold inInterval in H; simpl in *; lra. Qed.

(** If x is in i then the lower bound of i is less than or equal x.*) 
Lemma inIntervalLeLower: forall (i : Interval) (x : R),
  x [:] i -> lower i <= x.
Proof. intros [l u [|] [|]] x H; unfold inInterval in H; simpl in *; lra. Qed.

Lemma inIntervalLtUpper : forall (i : Interval) (r : R),
  r [:] i -> upperClosed i = false ->
  r < upper i.
Proof.
  intros [l u [|] [|]] r H C; unfold inInterval in H; simpl in *;
  try discriminate; lra.
Qed.

Lemma inIntervalLtLower : forall (i : Interval) (r : R),
  r [:] i -> lowerClosed i = false ->
  lower i < r.
Proof.
  intros [l u [|] [|]] r H C; unfold inInterval in H; simpl in *;
  try discriminate; lra.
Qed.

Lemma inAddLtLower : forall (i1 i2 : Interval) (r1 r2 : R),
  r1 [:] i1 -> r2 [:] i2 ->
  lowerClosed i1 = false \/ lowerClosed i2 = false ->
  lower i1 + lower i2 < r1 + r2.
Proof.
  intros [l1 u1 [|] [|]] [l2 u2 [|] [|]] r1 r2 H1 H2 [C | C];
  unfold inInterval in *; simpl in *; try discriminate; lra.
Qed.

Lemma inAddLtUpper : forall (i1 i2 : Interval) (r1 r2 : R),
  r1 [:] i1 -> r2 [:] i2 ->
  upperClosed i1 = false \/ upperClosed i2 = false ->
  r1 + r2 < upper i1 + upper i2.
Proof.
  intros [l1 u1 [|] [|]] [l2 u2 [|] [|]] r1 r2 H1 H2 [C | C];
  unfold inInterval in *; simpl in *; try discriminate; lra.
Qed.

Lemma addIntervalLower : forall (i1 i2 : Interval),
  lower (i1 [++] i2) = lower i1 + lower i2.
Proof. destruct i1, i2; reflexivity. Qed.

Lemma addIntervalUpper : forall (i1 i2 : Interval),
  upper (i1 [++] i2) = upper i1 + upper i2.
Proof. destruct i1, i2; reflexivity. Qed.

Lemma addIntervalUpperOpen : forall (i1 i2 : Interval),
  upperClosed (i1 [++] i2) = false ->
  upperClosed i1 = false \/ upperClosed i2 = false.
Proof.
  destruct i1, i2. simpl. intros. apply Bool.andb_false_iff.
  assumption.
Qed.

Lemma addIntervalLowerOpen : forall (i1 i2 : Interval),
  lowerClosed (i1 [++] i2) = false ->
  lowerClosed i1 = false \/ lowerClosed i2 = false.
Proof.
  destruct i1, i2. simpl. intros. apply Bool.andb_false_iff.
  assumption.
Qed.

Theorem inAddInterval : forall (i1 i2 : Interval) (r1 r2 : R),
  r1 [:] i1 -> r2 [:] i2 -> (r1 + r2) [:] (i1 [++] i2).
Proof.
  intros [l1 u1 [|] [|]] [l2 u2 [|] [|]] r1 r2 H1 H2;
  unfold inInterval in *; simpl in *; lra.
Qed.

(** Shifts an interval right by some amount i.e. adds that amount to the upper and lower
bounds of the interval. Closedness does not change.*)
Definition plusInterval (i : Interval) (r : R) : Interval :=
  match i with mkInterval l u cl cu=>
  mkInterval (l + r) (u + r) cl cu end.

(** Shifts an interval left by some amount i.e. adds that amount to the upper and lower
bounds of the interval.*)
Definition minusInterval (i : Interval) (r : R) : Interval :=
  match i with mkInterval l u cl cu=>
  mkInterval (l - r) (u - r) cl cu end.

Notation "i [+] r" := (plusInterval i r) (at level 45).
Notation "i [-] r" := (minusInterval i r) (at level 45).
Notation "[\ x , y \]" := (mkInterval x y true true).
Notation "[\ x , y \)" := (mkInterval x y true false).
Notation "(\ x , y \]" := (mkInterval x y false true).
Notation "(\ x , y \)" := (mkInterval x y false false).
Notation "i1 <[ i2" := (subInterval i1 i2) (at level 50).

(** Every interval can be rewritten by subtracting and then adding the same r.*)
Theorem minusPlusInterval : forall (i : Interval) (r : R),
  i = i [-] r [+] r.
Proof. intros. destruct i. simpl. f_equal; ring. Qed.

(** Every interval can be rewritten by adding and then subtracting the same r.*)
Theorem plusMinusInterval : forall (i : Interval) (r : R),
  i = i [+] r [-] r.
Proof. intros. destruct i. simpl. f_equal; ring. Qed.

(** Adding a negative is the same as subtracting*)
Theorem minusOppInterval : forall (i : Interval) (r : R),
  i [+] -r = i [-] r.
Proof. intros. destruct i. simpl. f_equal; ring. Qed.

Theorem inIntervalPlusCancel : forall (i : Interval) (x r : R),
  x + r [:] i [+] r -> x [:] i.
Proof.
  intros [l u [|] [|]] x r H;
  unfold inInterval in *; simpl in *; lra.
Qed.

Theorem inIntervalPlusCompat : forall (i : Interval) (x r : R),
  x [:] i -> x + r [:] i [+] r.
Proof. intros [l u [|] [|]] x r H; unfold inInterval in *; simpl in *; lra. Qed.

Theorem subIntervalPlusCancel : forall (i i' : Interval) (r : R),
  i [+] r <[ i' [+] r -> i <[ i'.
Proof.
  intros i i' r H x X.
  apply (inIntervalPlusCancel i' x r), H, inIntervalPlusCompat, X.
Qed.

(** Every interval is a sub interval of itself.*)
Lemma subIntervalRefl : forall (i : Interval), i <[ i.
Proof.
  unfold subInterval.
  intros; assumption.
Qed.


(** If a number is less than the lower bound of an interval then it is
not in that interval.*)
Lemma outIntervalLtLower : forall (r : R) (i : Interval),
  r < lower i -> ~ r [:] i.
Proof.
  unfold not; intros.
  apply inIntervalLeLower in H0. lra.
Qed.

(** If a number is greater than the upper bound of an interval then it is
not in that interval.*)
Lemma outIntervalLtUpper : forall (r : R) (i : Interval),
  upper i < r-> ~ r [:] i.
Proof.
  unfold not; intros.
  apply inIntervalLeUpper in H0. lra.
Qed.

(** If a number is less than or equal the lower bound of an interval
that is lower closed then it is not in the interval.*)
Lemma outIntervalLeLower : forall (r : R) (i : Interval),
  r <= lower i -> lowerClosed i = false -> ~ r [:] i.
Proof.
  unfold not; intros. eapply Rlt_not_le; try
  eapply inIntervalLtLower; try apply H1; assumption.
Qed.

(** If a number is less than or equal the lower bound of an interval
that is lower closed then it is not in the interval.*)
Lemma outIntervalLeUpper : forall (r : R) (i : Interval),
  upper i <= r -> upperClosed i = false -> ~ r [:] i.
Proof.
  unfold not; intros. eapply Rlt_not_le; try
  eapply inIntervalLtUpper; try apply H1; assumption.
Qed.

(** Membership of an interval is decidable.*)
Lemma inIntervalDec : forall (r : R) (i : Interval),
  r [:] i \/ ~ r [:] i.
Proof.
  intros.
  destruct i as [l u cl cu].
  destruct (total_order_T l r) as [[?|?]|?], (total_order_T r u) as [[?|?]|?];
  destruct cl, cu; unfold inInterval; simpl;
  first [left; lra | right; lra].
Qed.

(**If a number exists in the point interval [x, x]
then that number must be equal to x.*)
Lemma inIntervalPoint : forall (x y : R),
  x [:] [\y, y\] -> x = y.
Proof.
  intros. inversion H.
  eapply Rle_antisym; assumption.
Qed.

(*LOCAL TIDY*)

Ltac Rminus_refl_simpl := match goal with |- context [?x - ?x] =>
  replace (x - x) with 0; [ | ring] end.

Lemma Rminus_lt_subNonnegTot (a b : nonnegreal) c :
  0 < c -> a - b < c -> a -nn- b < c.
Proof. intros C H. unfold subNonnegTot. destruct (Rle_dec b a); simpl; lra. Qed.

Lemma Rminus_plus_lt_subNonnegTot (a b : nonnegreal) c z :
  z < c -> a - b + z < c -> a -nn- b + z < c.
Proof.
  intros.
  unfold subNonnegTot, zeroNonneg. destruct (Rle_dec b a); simpl; lra.
Qed.

Lemma subNonnegTot_le_Rminus_eq (r1 r2 : nonnegreal) :
  r2 <= r1 -> nonneg (r1 -nn- r2) = r1 - r2.
Proof.
  intros.
  unfold subNonnegTot. remember (Rle_dec r2 r1). destruct s.
  reflexivity. false.
Qed.

Lemma Rlt_double x : 0 < x -> x < x + x.
Proof. intro. lra. Qed.
  
Lemma Rmult_lt_0 y z : 0 < y -> 0 < z -> 0 < y * z.
Proof. intros. nra. Qed.

Lemma Rlt_le_zero_plus r1 r2 : 0 < r1 -> 0 <= r2 -> 0 < r1 + r2.
Proof. intros. lra. Qed.

Lemma Rmax_lt_l x y a : a < x -> a < Rmax x y.
Proof.
  intros.
  pose proof (Rmax_l x y). lra.
Qed.

Lemma subNonnegTot_0_or_Rminus r1 r2 :
  nonneg (r1 -nn- r2) = 0 \/
  nonneg (r1 -nn- r2) = r1 - r2.
Proof.
  unfold subNonnegTot.
  destruct (Rle_dec r2 r1). right. reflexivity.
  left. reflexivity.
Qed.

Lemma subNonnegTot_lt_0 (r1 r2 : nonnegreal) :
  r1 < r2 -> nonneg (r1 -nn- r2) = 0.
Proof.
  intros.
  unfold subNonnegTot. remember (Rle_dec r2 r1). destruct s.
  apply Rlt_not_le in H. false. reflexivity.
Qed.

Ltac Rplus3_swap_2_3_free := match goal with
  | |- context[?r1 + ?r2 + ?r3] => Rplus3_swap_2_3 r1 r2 r3 
  | |- context[?r1 + (?r2 + ?r3)] => rewrite <- Rplus_assoc;
    Rplus3_swap_2_3 r1 r2 r3
  end.

Lemma Rle_subNonnegTot_r (r1 r2 r3 : nonnegreal) :
  r1 <= r2 -> (r1 -nn- r3) <= (r2 -nn- r3).
Proof.
  intros.
  destruct (Rle_lt_dec r3 r1).
  rewrite !subNonnegTot_le_Rminus_eq; lra.
  rewrite subNonnegTot_lt_0 by assumption. apply cond_nonneg.
Qed.

Lemma addNonneg_subNonnegTot_le_assoc r1 r2 r3 :
  (r1 +nn+ r2) -nn- r3 <= r1 +nn+ (r2 -nn- r3).
Proof.
  pose proof (cond_nonneg r1). rewrite addNonnegFact.
  destruct (Rle_lt_dec r3 r2).
  rewrite !subNonnegTot_le_Rminus_eq; rewrite ?addNonnegFact; lra.
  rewrite (subNonnegTot_lt_0 r2 r3) by assumption.
  destruct (subNonnegTot_0_or_Rminus (r1 +nn+ r2) r3) as [E|E];
  rewrite E, ?addNonnegFact; lra.
Qed.

Lemma multNonneg_Rmult_eq r1 r2 :
  nonneg (r1 *nn* r2) = r1 * r2.
Proof.
  destruct r1, r2.
  reflexivity.
Qed.

Lemma subNonnegTot_le_Rminus (r1 r2 : nonnegreal) :
  r1 - r2 <= (r1 -nn- r2).
Proof.
  destruct (Rle_lt_dec r2 r1).
  rewrite subNonnegTot_le_Rminus_eq by assumption. lra.
  rewrite subNonnegTot_lt_0 by assumption. lra.
Qed.

Lemma subNonnegTot_plus_lt_Rminus (a b : nonnegreal) c z :
  a -nn- b + z < c -> a - b + z < c.
Proof.
  intros.
  pose proof (subNonnegTot_le_Rminus a b). lra.
Qed.

(*-LOCAL TIDY*)
