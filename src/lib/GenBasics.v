(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** General basics that know nothing about the Comhordu model: times, delays and
distances, and helpers for natural numbers, lists and sets.*)

Require Import ComhCoq.lib.Extras.LibTactics.
From Stdlib Require Import Reals Arith Lia.

(*********Imports********)
From Stdlib Require Export List.
(**Notations stolen from tutorial.*)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "e _: n" := (In e n) (at level 60).
From Stdlib Require Export Logic.Decidable.
Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
From Stdlib Require Import Lists.ListSet.


(*********Basic Stuff********)

Definition toNonneg (r : posreal) : nonnegreal :=
  let h := (Rlt_le 0 r (cond_pos r)) in
  mknonnegreal r h.

(** A time value is a non negative real number.*)
Record Time := mkTime {time :> nonnegreal}.

Definition zeroTime : Time := mkTime zeroNonneg.

(**Solves the goal 0 <= u where u is some time.*)
Ltac timeNonneg := 
  match goal with
  | [ |- 0 <= (nonneg (time ?t))] => unwrap2_apply2 t
  | [ |- (nonneg (time zeroTime)) <= (nonneg (time ?t))] => simpl;unwrap2_apply2 t
  end.

(** A delay is a positive real number.*)
Record Delay := mkDelay {delay :> posreal}.

(**Solves the goal 0 < u where u is some delay.*)
Ltac delPos :=
  match goal with
  | [ |- 0 < (pos (delay ?d))] => unwrap2_apply2 d
  | [ |- (nonneg (time zeroTime)) < (pos (delay ?d))] => simpl;unwrap2_apply2 d
  end.

(** We can coerce a delay to be a time.*)
Coercion delToTime (d : Delay) : Time :=
  match d with mkDelay d0 =>
    mkTime d0 end.

(** A distance is a non negative real number*)
Record Distance := mkDistance {distance :> nonnegreal}.

Ltac foldDist l l0 H := replace (dist_euc (xCoord l) (yCoord l) (xCoord l0) (yCoord l0)) with
  (nonneg (dist2d l l0)) in H;[ | simpl;ring].

Definition distFun p1 p2 := mkDistance (dist2d p1 p2).

Lemma timeEqNonneg : forall (t1 t2 : Time), (time t1) = (time t2) -> t1 = t2.
  destruct t1, t2. simpl. intros. f_equal. assumption. Qed.

Lemma timeEqR : forall (t1 t2 : Time), (nonneg (time t1)) = (nonneg (time t2)) ->
  t1 = t2. intros. apply timeEqNonneg. apply nonnegRealEqR. assumption. Qed.

Lemma delayEqPos : forall (d1 d2 : Delay), delay d1 = delay d2 -> d1 = d2.
  destruct d1, d2. simpl. intros. f_equal. apply H. Qed.

Lemma delayEqR : forall (d1 d2 : Delay), pos d1 = pos d2 -> d1 = d2.
  intros. apply delayEqPos. apply posRealEqR. assumption. Qed.

Open Scope nat_scope.

Lemma lt_notEq : forall (n m : nat),
  n < m -> n <> m. intros. lia. Qed.

(** Converts a decidable proposition to a boolean.*)
Definition decToBool {P : Prop} (p : {P} + {~P}) : bool :=
  match p with
  | left _ => true
  | right _ => false
  end.
   
(** Converts a decidable relation to a boolean.*)
Definition decToOption {P : Prop} (p : {P} + {~P}) : option P :=
  match p with
  | left P => Some P
  | right _ => None
  end.

Lemma lt_plus_r (m n : nat) :
  0 < n -> m < m + n. intros. lia. Qed.

Lemma lt_plus_l (m n : nat) :
  0 < n -> m < n + m. intros. lia. Qed.

Lemma le_plus_r (m n : nat) :
  m <= m + n. intros. lia. Qed.

Lemma le_plus_l (m n : nat) :
  m <= n + m. intros. lia. Qed.

Open Scope R_scope.

(** inAtList a i l says that a is at position i in the list l.
The first position is position 0.*)
Inductive inAtList {A : Type} (a : A) : nat -> list A -> Prop :=
  | inatlFst (l : list A) :
    inAtList a 0 (a :: l)
  | inatlCons (i : nat) (a' : A) (l : list A) :
    inAtList a i l -> inAtList a (S i) (a' :: l).

Notation "a -@ i -: l" := (inAtList a i l) (at level 50).

(** If an element is in a list according to the definition of inAtList,
then it is in the list according to In.*)
Theorem inAtList_inList (A : Type) (a : A) (l : list A) (i : nat) :
  a -@ i -: l -> a _: l. intros. induction H. constructor. reflexivity.
  simpl. right. assumption. Qed.

(** If a is at i in l and so is a', then a = a'.*)
Theorem inAtListUnique (A : Type) (a a' : A) (i : nat) (l : list A) :
  a -@ i -: l -> a' -@ i -: l -> a = a'. intros. induction H.
  inversion H0. reflexivity. inversion H0. apply IHinAtList. assumption. Qed.

(** There either exists an element at position i or there doesn't.*)
Theorem decInAtList (A : Type) (i : nat) (l : list A) :
  decidable (exists a, a -@ i -: l). unfold decidable.
  intros. generalize dependent i. induction l; intros.
  right. intro. inversion H. inversion H0. destruct i.
  left. exists a. constructor. addHyp (IHl i).
  inversion H; clear H. inversion H0 as [e He]. left.
  exists e. apply inatlCons. assumption. right. intro.
  inversion H as [e He]. clear H. inversion He. apply H0. exists e.
  assumption. Qed.

(**Equality is decidable for times.*)
Lemma eqDecTime : eqDec Time. unfold eqDec. destruct x1, x2.
  generalize (eqDecNonnegReal time0 time1). intros. inversion H.
  left. f_equal. assumption. right. unfold not; intros. apply H0.
  inversion H1. reflexivity. Qed.

(** Equality is decidable on Delays.*)
Lemma eqDecDelay : eqDec Delay. unfold eqDec. destruct x1, x2.
  generalize (eqDecPosReal delay0 delay1). intros. inversion H.
  left. f_equal. assumption. right. unfold not; intros. apply H0.
  inversion H1. reflexivity. Qed.

Lemma eqDecDistance : eqDec Distance. unfold eqDec. destruct x1, x2.
  generalize (eqDecNonnegReal distance0 distance1). intros. inversion H.
  left. f_equal. assumption. right. unfold not; intros. apply H0.
  inversion H1. reflexivity. Qed.

(**Returns t1 - t2, or None if t1 < t2.*)
Definition subtractTime (t1 t2 : Time) : option Time :=
  let r1 := nonneg t1 in let r2 := nonneg t2 in
  match total_order_T r1 r2 with
  | inleft _ => None
  | inright H => Some (mkTime (mknonnegreal (r1 - r2)
    (Rlt_le 0 (r1 - r2) (RltMinusBothSides r1 r2 H))))
  end.

Definition addTime (t1 t2 : Time) : Time :=
  let r1 := nonneg t1 in let r2 := nonneg t2 in
  mkTime (mknonnegreal (r1 + r2) (Rle_zero_plus r1 r2 (cond_nonneg t1) (cond_nonneg t2))).

(** Add two delays together to get a third delay.*)
Definition addDelay (d1 d2 : Delay) : Delay :=
  let r1 := pos d1 in let r2 := pos d2 in
  mkDelay (mkposreal (r1 + r2) (Rlt_zero_plus r1 r2 (cond_pos d1) (cond_pos d2))).

(** Add a delay to a time to get a delay.*)
Definition addDelayTime (t : Time) (d : Delay) : Delay :=
  let r1 := nonneg t in let r2 := pos d in
  mkDelay (mkposreal (r1 + r2) (Rplus_le_lt_0_compat r1 r2 (cond_nonneg t) (cond_pos d))).

Notation "t +dt+ d" := (addDelayTime t d) (at level 45).
Notation "d +d+ d'" := (addDelay d d') (at level 45).

Lemma addDelayComm : forall (d d' : Delay), d +d+ d' = d' +d+ d.
  destruct d, d'. unfold addDelay. repeat f_equal.
  apply posRealEqR. simpl. apply Rplus_comm. Qed.

(**If there is some delays d and d', and they are being
added with the left one as a time, then they can be added as normal.*)
Lemma timeDelAddSwitch : forall (d d' : Delay),
  d +dt+ d' = d +d+ d'. intros. unfold addDelayTime.
  unfold addDelay. f_equal. apply posRealEqR. simpl.
  destruct d. destruct delay0. reflexivity. Qed.

Lemma delTimeAddAssoc : forall (t : Time) (d d' : Delay),
  t +dt+ d +dt+ d' = t +dt+ (d +dt+ d'). intros.
  destruct t, d, d'. destruct time0, delay0, delay1.
  unfold addDelayTime. simpl. repeat f_equal.
  apply posRealEqR. simpl. apply Rplus_assoc. Qed.

Lemma delTimeAddAssoc2 : forall (t : Time) (d d' : Delay),
  (t +dt+ d) +d+ d' = t +dt+ (d +d+ d'). intros.
  repeat rewrite <- timeDelAddSwitch. apply delTimeAddAssoc. Qed.

Lemma timeDelAddZeroL : forall (d : Delay),
  zeroTime +dt+ d = d. unfold zeroTime. destruct d.
  unfold addDelayTime. f_equal. apply posRealEqR.
  simpl. ring. Qed.

(** If a delay d is less than or equal a time t,
then there is some time t' such that t = t' + d.*)
Lemma delLeTimeSum : forall (t : Time) (d : Delay),
  d <= t -> exists t', t = t' +dt+ d. intros.
  assert (exists r, nonneg (time t) = d + r /\ 0 <= r).
  exists (t - d). split. ring. replace 0 with (t - t).
  apply Rplus_le_compat. apply Rle_refl.
  apply Ropp_le_contravar. assumption. ring.
  invertClear H0. invertClear H1.
  exists (mkTime (mknonnegreal x H2)). destruct t, d.
  apply timeEqR. simpl. rewrite Rplus_comm. apply H0.
  Qed.

(** Subtract d2 from d1. Requires a proof that d2 is indeed less than d1 so
that the result is a delay.*)
Definition minusDelay (r1 r2 : R) (p : r2 < r1) : Delay :=
   mkDelay (mkposreal (r1 - r2) (Rgt_minus r1 r2 (Rlt_gt r2 r1 p))).

(** Subtracting and then adding the same delay gives the same result.*)
Lemma minusAddDelay : forall (d1 d2 : Delay) (p : d2 < d1),
  (minusDelay d1 d2 p) +d+ d2 = d1. intros. apply delayEqR. simpl. ring. Qed.

(** Adding a time that has been subtracted gives back the original result.*)
Lemma minusDelayAddTime : forall (d : Delay) (t : Time) (p : t < d),
  d = t +dt+ (minusDelay d t p). intros. apply delayEqR. simpl. ring. Qed.

(**The right summand in a sum of delays is less than the total sum.*)
Lemma addDelayLtR : forall (d1 d2 : Delay),
  d2 < d1 +d+ d2. destruct d1, d2. destruct delay0, delay1.
  simpl. rewrite <- Rplus_comm. cut (pos0 + 0 < pos0 + pos).
  rewrite Rplus_0_r. intros. assumption. apply Rplus_lt_compat_l.
  assumption. Qed.

(** Adding and then subtracting the same quantity leaves the original delay.*)
Lemma addMinusDelay : forall (d1 d2 : Delay),
  exists p, minusDelay (d1 +d+ d2) d2 p = d1.
  intros. exists (addDelayLtR d1 d2). destruct d1, d2.
  destruct delay0, delay1. apply delayEqR. simpl. ring. Qed.

(** Communtativity of times in a sum of three terms.*)
Lemma timeDelAddComm : forall (t1 t2 : Time) (d : Delay),
  t1 +dt+ (t2 +dt+ d) = t2 +dt+ (t1 +dt+ d). intros.
  apply delayEqR. simpl. ring. Qed.

(**Subtract R2 from R1. Requires a proof that R2 is indeed less
than or equal r1 so that the result is a Time.*)
Definition minusTime (r1 r2 : R) (p : r2 <= r1) : Time :=
   mkTime (mknonnegreal (r1 - r2) (Rge_le (r1 - r2) 0
   (Rge_minus r1 r2 (Rle_ge r2 r1 p)))).

(** To show that d = d +d+ d' according to the addDel function, it suffices to show that
d = d + d' i.e. that the real parts and real number addition equates.*)
Lemma addRaddDel : forall (d d' d'' : Delay),
  pos d = d' + d'' -> d = d' +d+ d''. intros.
  apply delayEqR. simpl. apply H. Qed.

(** Every delay has two delays that add up to make it.*)
Theorem addDelayExists : forall (d : Delay),
  exists d1 d2, d = d1 +d+ d2. intros.
  destruct d as [r]. addHyp (addPosRealExists r). invertClear H.
  invertClear H0. exists (mkDelay x). exists (mkDelay x0).
  apply addRaddDel. apply H. Qed.

Lemma RMax_time (t1 t2 : Time) : 0 <= Rmax t1 t2.
  eapply Rle_trans;[ |apply Rmax_l]. timeNonneg. Qed.
  
(*Returns the maximum of two times.*)
Definition timeMax (t1 t2 : Time) : Time :=
  mkTime (mknonnegreal (Rmax t1 t2) (RMax_time t1 t2)).
 
(*The timeMax function is correct.*)
Lemma timeMax_RMax : forall (t1 t2 : Time), nonneg (timeMax t1 t2) = Rmax t1 t2.
  intros. reflexivity. Qed.
Notation "t1 +t+ t2" := (addTime t1 t2) (at level 50).

(** Given time t, splits goal into two subgoals based on whether 0 = t or 0 < t*)
Ltac timezerolteq t U := let H := fresh in assert (0 <= t) as H;[timeNonneg| ];
  apply Rle_lt_or_eq_dec in H; let U1 := fresh U in elim_intro H U1 U1.

Ltac mkdel t Q d' := remember (mkDelay (mkposreal t Q)) as d'.

Ltac timering := apply timeEqR; simpl; ring.

Open Scope nat_scope.

(********* More Stuff ********)


Open Scope nat_scope.

(**If a property p is true of the number j, and j <= k, then there is some
largest j' between j and k such that p is true at j'.*)
Theorem rightmost : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  p j -> j <= k ->
  exists j', j <= j' <= k /\ p j' /\
  forall x : nat, j' < x <= k -> ~ p x. intros.
  induction H0. exists j. split. split; apply Nat.le_refl.
  split. assumption. intros. inversion H0. apply False_ind.
  eapply (proj1 (Nat.lt_nge _ _)). apply H1. assumption.
  invertClear IHle. addHyp (K (S m)). invertClear H2.
  exists (S m). split. split. constructor. assumption. apply Nat.le_refl.
  split. assumption. intros. invertClear H2. apply False_ind.
  eapply (proj1 (Nat.lt_nge _ _)). apply H4. assumption. exists x.
  invertClear H1. invertClear H4. split. invertClear H2.
  split. assumption. constructor. assumption. split.
  assumption. intros. invertClear H4. invertClear H7.
  assumption. apply H5; split; assumption. Qed.

Open Scope R_scope.

Lemma plusIntervalZero : forall (i : Interval),
  i [+] zeroTime = i. intros. destruct i. unfold zeroTime.
  simpl. f_equal; ring. Qed.

Open Scope nat_scope.

(**The same theorem as rightmost but with negation of P as existential and P as
universal properties.*)
Theorem rightmostNeg : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  ~p j -> j <= k ->
  exists j', j <= j' <= k /\ ~p j' /\
  forall x : nat, j' < x <= k -> p x. intros.
  assert (forall a, ~(~(p a)) -> p a). intros.
  addHyp (K a). invertClear H2. apply H3. apply False_ind.
  apply H1. assumption. assert (forall a, decidable (~ p a)).
  intros. apply dec_not. apply K.
  addHyp (rightmost j k (fun j => ~p j) H2 H H0).
  invertClear H3. rename x into j'. exists j'. invertClear H4.
  invertClear H5. split. assumption. split. assumption. intros.
  apply H1. apply H6. assumption. Qed.   

(**This characterisation of le leaves does the inductive part by
subtracting from the lesser number rather than adding to the larger
one, and makes certain proofs easier.*)
Inductive leAlt : nat -> nat-> Prop :=
  | leaRefl : forall (n : nat), leAlt n n
  | leaSucc : forall (m n : nat), leAlt (S m) n -> leAlt m n.

(**This is the key difference between leAlt and le.*)
Lemma leAlt_S : forall (m n : nat), leAlt m n -> leAlt m (S n).
  intros. induction H. repeat constructor. constructor.
  assumption. Qed. 

(*The alternative characterisation of le coindices with
the standard one.*)
Lemma leAltLe : forall (m n : nat), m <= n <-> leAlt m n.
  intros. split; intros. induction H. constructor.
  apply leAlt_S. assumption. induction H. constructor.
  apply le_S_n. constructor. assumption. Qed.  

(**If a property p is true of the number k, and j <= k,
then there is some smallest j' between j and k such that p is true at j'.*)
Theorem leftmost : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  p k -> j <= k ->
  exists j', j <= j' <= k /\ p j' /\
  forall x : nat, j <= x < j' -> ~ p x. intros.
  rewrite leAltLe in H0. induction H0.
  exists n. split. split; apply Nat.le_refl.
  split. assumption. intros. inversion H0. apply False_ind.
  eapply (proj1 (Nat.lt_nge _ _)). apply H2. assumption. apply IHleAlt in H.
  clear IHleAlt. invertClear H. addHyp (K (m)).
  invertClear H1. invertClear H3. invertClear H.
  exists m. split. split. constructor. rewrite leAltLe.
  constructor. assumption. split. assumption.
  intros. invertClear H. unfold not. intros. eapply (proj1 (Nat.lt_nge _ _)).
  apply H6. assumption. exists x. split. invertClear H2. split.
  apply le_S_n. constructor. assumption. assumption.
  split. assumption. intros. invertClear H.
  invertClear H5. rewrite <- H. assumption.
  apply H4. split. apply le_n_S. assumption.
  rewrite H7. assumption. Qed.

(**The same theorem as leftmost but with
negation of P as existential and P as universal properties.*)
Theorem leftmostNeg : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  ~p k -> j <= k ->
  exists j', j <= j' <= k /\ ~p j' /\
  forall x : nat, j <= x < j' -> p x. intros.
  assert (forall a, ~(~(p a)) -> p a). intros.
  addHyp (K a). invertClear H2. apply H3. apply False_ind.
  apply H1. assumption. assert (forall a, decidable (~ p a)).
  intros. apply dec_not. apply K.
  addHyp (leftmost j k (fun j => ~p j) H2 H H0).
  invertClear H3. rename x into j'. exists j'. invertClear H4.
  invertClear H5. split. assumption. split. assumption. intros.
  apply H1. apply H6. assumption. Qed. 

(**If p is true at j and j <= k, then there is some rightmost
j' such that p is true from j to j' and either ~p is true at j'+1 or j' = k.*)
Theorem rightmostCont : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  p j -> j <= k ->
  exists j' , j <= j' <= k /\ 
  forall m : nat, j <= m <= j' -> p m /\
  (~p (S j') \/ j' = k). intros. induction H0.
  exists j. split. split; constructor. intros. split.
  assert (m = j). invertClear H0.
  apply Nat.le_antisymm; assumption. rewrite H1. assumption.
  right. reflexivity. invertClear IHle. invertClear H1.
  rename x into j'. invertClear H2.
  apply le_lt_eq_dec in H4. invertClear H4.
  (*Case j' < m*) 
  exists j'. split. split. assumption.
  constructor. ltToLe H2. assumption. intros.
  rename m0 into n. addHyp (H3 n H4). clear H3.
  invertClear H5. split. assumption. invertClear H6.
  left. assumption. apply False_ind. rewrite <- H5 in H2.
  eapply Nat.lt_irrefl. apply H2.
  (*Case j' = m*)
  addHyp (K (S m)). invertClear H4.
  (*Case p is true at the last p*)
  exists (S m). split.
  split. constructor. rewrite <- H2. assumption. constructor.
  intros. invertClear H4. apply le_lt_eq_dec in H7.
  invertClear H7. rename m0 into n. rewrite H2 in H3.
  addHyp (H3 n). assert (j <= n <= m). split. assumption.
  apply le_S_n. apply H4. addHyp (H7 H8). clear H7.
  invertClear H9. split. assumption. right. reflexivity.
  split. rewrite H4. assumption. right. reflexivity.
  (*Case p is not true at the last p*)
  exists j'. split. split. assumption. rewrite H2.
  repeat constructor. intros n Q.
  addHyp (H3 n Q). invertClear H4. split. assumption.
  invertClear H7. left. assumption. left.
  rewrite H4. assumption. Qed.

Open Scope R_scope.

(**If u = 0 as a real, then u = zeroTime.*)
Lemma timeZero : forall (u : Time),
  (nonneg (time u)) = 0 -> u = zeroTime. intros.
  unfold zeroTime. destruct u. f_equal. destruct time0.
  unfold zeroNonneg. simpl in H. generalize dependent cond_nonneg.
  rewrite H. intros. f_equal. apply proof_irrelevance. Qed.

(*****Incl stuff******)

Lemma inclNotEx {A : Type} (l1 l2 : list A) : (forall x y : A, {x = y} + {x <> y}) ->
  ~ incl l1 l2 -> exists a, a _: l1 /\ ~a _: l2. intros. induction l1.
  apply False_ind. apply H. unfold incl. intros. inversion H0.
  addHyp (in_dec X a l2). invertClear H0. assert (~ incl l1 l2).
  unfold not. intro. apply H. unfold incl. intros. inversion H2.
  rewrite <- H3. assumption. apply H0. apply H3. apply IHl1 in H0.
  invertClear H0. exists x. invertClear H2. split. apply in_cons.
  assumption. assumption. exists a. split. constructor. reflexivity.
  assumption. Qed. 

Lemma incl_emp {A : Type} (l : list A) : incl [] l. unfold incl. intros.
  inversion H. Qed.

Lemma incl_emp_eq {A : Type} (l : list A) : incl l [] -> l = []. intros.
  unfold incl in H. destruct l. reflexivity. addHyp (H a).
  cut (a _: []). intros. inversion H1. apply H0. constructor.
  reflexivity. Qed.

Lemma diff_emp {A : Type} (l : list A)
  (p : forall x y : A, {x = y} + {x <> y}) : set_diff p l [] = [] -> l = [].
  intros. destruct l. reflexivity. inversion H. apply set_add_not_empty in H1.
  inversion H1. Qed.

Lemma incl_diff_equiv {A : Type} (l1 l2 : list A)
  (p : forall x y : A, {x = y} + {x <> y}) : incl l1 l2 <-> set_diff p l1 l2 = [].
  split; intros. unfold incl in H. remember (set_diff p l1 l2) as l.
  destruct l. reflexivity. apply False_ind. cut (~a _: l2). intros. apply H0.
  apply H. apply set_diff_elim1 with (Aeq_dec := p) (y := l2). rewrite <- Heql.
  constructor. reflexivity. apply set_diff_elim2 with (Aeq_dec := p) (x := l1).
  rewrite <- Heql. constructor. reflexivity.
  unfold incl. intros. addHyp (in_dec p a l2). invertClear H1. assumption.
  addHyp (set_diff_intro p a l1 l2 H0 H2). rewrite H in H1. inversion H1. Qed.

Lemma decIncl {A : Type} (l1 l2 : list A) :
  (forall x y : A, {x = y} + {x <> y}) -> decidable (incl l1 l2).
  intros. remember (set_diff X l1 l2) as l. destruct l. left.
  rewrite incl_diff_equiv. symmetry. apply Heql.
  right. unfold not. intro. rewrite incl_diff_equiv with (p := X) in H.
  rewrite <- Heql in H. inversion H. Qed.

Lemma inter_incl {A : Type} (x y z : set A)
  (p : forall a b : A, {a = b} + {a <> b}) :
  incl x y -> incl (set_inter p x z) (set_inter p y z). intros.
  unfold incl. intros. addHyp H0. apply set_inter_elim1 in H0.
  apply set_inter_elim2 in H1. apply H in H0. apply set_inter_intro;
  assumption. Qed.  

(*****END : Incl stuff******)


(*****Set stuff******)

Lemma set_inter_nil_cons {X : Type}
  {p : forall x y : X, {x = y} + {x <> y}} (l1 l2 : list X) (x : X) :
  set_inter p (x :: l1) l2 = [] -> set_inter p l1 l2 = [].
  intros. remember (set_inter p l1 l2). destruct s. reflexivity.
  assert (x0 _: set_inter p l1 l2). rewrite <- Heqs. constructor.
  reflexivity. apply set_inter_elim in H0. invertClear H0.
  assert (x0 _: (x :: l1)). unfold In. right. apply H1.
  assert (x0 _: []). rewrite <- H. apply set_inter_intro.
  apply H0. assumption. inversion H3. Qed.

Lemma set_inter_nil_in1 {X : Type}
  {p : forall x y : X, {x = y} + {x <> y}} (l1 l2 : list X) (x : X) :
  set_inter p l1 l2 = [] -> x _: l1 -> ~x _: l2. intros.
  generalize dependent l2. induction l1; unfold not; intros.
  inversion H0. inversion H0. assert (a _: []). rewrite <- H.
  apply set_inter_intro. rewrite <- H2 in H0. assumption.
  rewrite H2. assumption. inversion H3.
  eapply IHl1. apply H2. eapply set_inter_nil_cons. apply H.
  assumption. Qed.  

Lemma set_inter_nil_in2 {X : Type}
  {p : forall x y : X, {x = y} + {x <> y}} (l1 l2 : list X) (x : X) :
  set_inter p l1 l2 = [] -> x _: l2 -> ~x _: l1. unfold not. intros.
  generalize H0. eapply set_inter_nil_in1. apply H. assumption. Qed.

(*****END : Set stuff******)


(*****Steps at a position in a list******)

(** Two lists that agree except at position i, where their elements are related by R.*)
Inductive stepAt {A : Type} (R : A -> A -> Prop) : nat -> list A -> list A -> Prop :=
  | stepAtHd (x x' : A) (l : list A) : R x x' -> stepAt R 0 (x :: l) (x' :: l)
  | stepAtTl (i : nat) (x : A) (l l' : list A) :
    stepAt R i l l' -> stepAt R (S i) (x :: l) (x :: l').

(** Each position is unchanged or related.*)
Lemma stepAt_Forall2 {A : Type} (R : A -> A -> Prop) i l l' :
  stepAt R i l l' -> Forall2 (fun x x' => x = x' \/ R x x') l l'.
Proof.
  intro S. induction S as [x x' l H | i x l l' S IH].
  - constructor; [right; assumption | ].
    induction l; constructor; [left; reflexivity | assumption].
  - constructor; [left; reflexivity | assumption].
Qed.

(** After steps at two different positions, each position is unchanged or related by one
of the two.*)
Lemma stepAt_stepAt_Forall2 {A : Type} (R1 R2 : A -> A -> Prop) i j l l' l'' :
  i <> j -> stepAt R1 i l l' -> stepAt R2 j l' l'' ->
  Forall2 (fun x x' => x = x' \/ R1 x x' \/ R2 x x') l l''.
Proof.
  intros N S1. revert j l'' N. induction S1 as [x x' l H | i x l l' S1 IH]; intros j l'' N S2;
    inversion S2; subst.
  - exfalso. apply N. reflexivity.
  - constructor; [auto | ].
    match goal with [K : stepAt _ _ ?m ?m' |- Forall2 _ ?m ?m'] =>
      apply stepAt_Forall2 in K; revert K; apply Forall2_impl; simpl; tauto end.
  - constructor; [auto | ]. apply stepAt_Forall2 in S1. revert S1. apply Forall2_impl.
    simpl. tauto.
  - constructor; [auto | ].
    match goal with [K : stepAt _ _ l' _ |- _] => eapply IH; [ | exact K] end.
    intro E. apply N. f_equal. assumption.
Qed.

(** A step under one relation is a step under any larger one.*)
Lemma stepAt_impl {A : Type} (R R' : A -> A -> Prop) i l l' :
  (forall x x', R x x' -> R' x x') -> stepAt R i l l' -> stepAt R' i l l'.
Proof. intros H S. induction S; constructor; auto. Qed.

(** The elements at the step's position are related.*)
Lemma stepAt_nth_error_eq {A : Type} (R : A -> A -> Prop) i l l' : stepAt R i l l' ->
  exists x x', nth_error l i = Some x /\ nth_error l' i = Some x' /\ R x x'.
Proof. intro S. induction S; simpl; eauto. Qed.

(** Every other position is as it was.*)
Lemma stepAt_nth_error_neq {A : Type} (R : A -> A -> Prop) i j l l' : stepAt R i l l' ->
  j <> i -> nth_error l j = nth_error l' j.
Proof.
  intro S. revert j. induction S as [x x' l H | i x l l' S IH]; intros [ |j] N; simpl;
    [exfalso; apply N; reflexivity | reflexivity | reflexivity | ].
  apply IH. intro E. apply N. f_equal. exact E.
Qed.

(** Inverts every stepAt and Forall2 hypothesis over a list of known shape, splitting a step
at an unknown position into one case per position, until the lists are explicit.*)
Ltac positions_inv := repeat match goal with
  | [H : stepAt _ _ [] _ |- _] => inversion H
  | [H : stepAt _ _ (_ :: _) _ |- _] => inversion H; subst; clear H
  | [H : Forall2 _ [] _ |- _] => inversion H; subst; clear H
  | [H : Forall2 _ (_ :: _) _ |- _] => inversion H; subst; clear H
  end; cbv beta in *.

(** A relation that holds between each element and itself holds pointwise along a list.*)
Lemma Forall2_diag {A : Type} (R : A -> A -> Prop) (l : list A) :
  (forall x, In x l -> R x x) -> Forall2 R l l.
Proof.
  induction l as [ |x l IH]; intro H; constructor.
  - apply H. left. reflexivity.
  - apply IH. intros y I. apply H. right. assumption.
Qed.

(** Two pointwise relations compose along lists.*)
Lemma Forall2_compose {A B C : Type} (R : A -> B -> Prop) (S : B -> C -> Prop)
  (l1 : list A) (l2 : list B) (l3 : list C) :
  Forall2 R l1 l2 -> Forall2 S l2 l3 -> Forall2 (fun x z => exists y, R x y /\ S y z) l1 l3.
Proof.
  intro F. revert l3. induction F as [ |x y l1 l2 Rxy F IH]; intros l3 G;
    inversion G; subst; constructor; eauto.
Qed.

(*****END : Steps at a position in a list******)
