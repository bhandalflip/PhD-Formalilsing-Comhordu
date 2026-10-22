(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lra.
Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.GenTacs. 
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults. 
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.ProtocolBridge.

(* begin helpers for state_disj_paused_notifAbort *)
(* Given D : discActEnabled q a, where q is (bisimilar-free) concrete protocol
   state term, unfold q and invert every transition, closing the goal when q
   cannot perform a. *)
Ltac state_disj_paused_notifAbort_dae_contra D :=
  let q := fresh "q" in let TR := fresh "TR" in
  destruct D as [q TR];
  unfold rangeBad, currOK, abortOvlp, paused, tfsCurr, tfsStart, tfsNext, tfsBc,
    switchListen, switchBc, switchCurr, ovReady, ovWait, init, dormant in TR;
  repeat (match goal with [T : stepDiscProc _ _ _ |- _] =>
    inversion T; clear T; subst end).

(* Given RS : X p (with X p unfolding to p ~p~ q) and PU : discActEnabled p a,
   derive a contradiction when q cannot perform a. *)
Ltac state_disj_paused_notifAbort_bisim_contra RS PU :=
  let D := fresh "D" in
  lets D : bisim_dae RS PU; state_disj_paused_notifAbort_dae_contra D.
(* end helpers *)

Section NARMisc.
Context {Model : ComhModel}.

Lemma state_disj_paused_notifAbort i n :
  pausedStateNet i n -> notifAbortPathNet i n -> False.
Proof.
  intros U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst.
  lets PU : paused_unpause_in PS. clear PS.
  inversion V1; subst;
  first [ match goal with [X : rangeBadStateProt _ _ |- _] => inversion X; subst end
        | match goal with [X : currOKStateProt _ _ |- _] => inversion X; subst end
        | match goal with [X : abortOvlpStateProt _ |- _] => inversion X; subst end ];
  match goal with [RS : _ p3 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_start : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> tfsStartStateNet i n -> False.
Proof.
  intros i n U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_abort_in PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_bc : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> tfsBcStateNet i n -> False.
Proof.
  intros i n U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_abort_in PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_switchListen : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> switchListenStateNet i n -> False.
Proof.
  intros i n U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_abort_in PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_dormant : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> dormantStateNet i n -> False.
Proof.
  intros i n U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_mCurr_out PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_tfsNext : forall (i : nat) (n : Network) (m : Mode),
  tfsCurrStateNet i n -> tfsNextStateNet m i n -> False.
Proof.
  intros i n m U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_abort_in PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

(*The following string of results should be provable by lifting inter-component
relationships. Except the one with nextSince, not so sure there.*)
Lemma ovWait_ovReady_nextMode_net i n (p : reachableProtNet n) :
  (forall m t x y, ovWaitStateNet m t x y i n ->
   nextModeNet m i n) /\
  (forall m t l, ovReadyStateNet m t l i n -> nextModeNet m i n).
Proof.
  split; intros.
  - eapply ComhCoq.protocol.NetAuxBasics.ovWaitState_nextMode_net; eassumption.
  - eapply ComhCoq.protocol.NetAuxBasics.ovWait_ovReady_nextMode_net
      with (x := zeroTime) (y := zeroTime); [exact p | right; eassumption].
Qed.
(*+*)

Lemma switchBc_nextMode_net m i n :
  reachableProtNet n -> switchBcStateNet m i n -> nextModeNet m i n.
Proof.
  (* overlap_nextMode_ent, lifted to the entity in question. *)
  intros R SB. net_state_destr SB p1 p2 p3 l h k E.
  destruct (overlap_nextMode_ent _ (reachableNet_ent _ _ _ _ R E) _ _ _ _ _ _ eq_refl)
    as [_ [_ [_ IB]]].
  eapply lenWitness; [ | exact E]. exact (IB _ SB).
Qed.
(*+*)

(** An entity nextSince m has m as its next mode.*)
Lemma nextSince_next : forall (m : Mode) (t : Time) (i : nat)
  (n : Network) (p : reachableProtNet n),
  nextSince m t i n p -> nextModeNet m i n.
Proof.
  intros m t i n p NS.
  induction NS as [a i n n' p w l t t' x y PND OR OW | a t i n n' p w NS IH NSS
    | d t i n n' p w NS IH].
  - exact (proj1 (ovWait_ovReady_nextMode_net i n' (reachNetDisc n n' a p w)) m t' x y OW).
  - destruct IH as [e NM E].
    destruct (link_net_ent_disc_fwd _ _ _ _ _ w E) as [e' [E' _]].
    destruct e as [q l h k]. destruct e' as [q' l' h' k']. simpl in NM.
    destruct (eqDecModeState k k') as [EQ | NE].
    + subst k'. eapply lenWitness; [ | exact E']. exact NM.
    + exfalso.
      assert (M : mState_in_net k i n) by (econstructor; exact E).
      assert (M' : mState_in_net k' i n') by (econstructor; exact E').
      destruct (mState_switch_states _ _ _ _ _ _ p (nextMode_unstable _ _ NM) NE w M M')
        as [[_ Y] | [[_ Y] | [[_ Y] | [m0 [_ Y]]]]].
      (* each is a state that no nextSince state is bisimilar to *)
      all: net_state_destr NSS q1 q2 q3 l1 h1 k1 EN.
      all: net_state_ent Y EN.
      all: destruct NSS as [m1 t1 x1 y1 W | m1 t1 l2 W | m1 W | m1 W].
      all: pose proof (bisim_trans _ _ _ (bisim_symm _ _ W) Y) as BT;
        prot_outProc_in_not_body; try unfold liftVarList in BT; refute_by_chan BT.
  - eapply nextModeNet_del_pres; eassumption.
Qed.
(**Proof: Strtengthen the statement to replace nextSince with nextSinceState.
Then split into the different nextSinceState cases and use an aux lemma for each.*)

(** An entity has at most one next mode.*)
Local Lemma nextModeNet_unique m m' i n : nextModeNet m i n -> nextModeNet m' i n -> m = m'.
Proof.
  intros [e NM E] NM'. lets NM2 : liftEntNet_ent NM' E. simpl in NM2.
  rewrite NM in NM2. injection NM2 as EQ. exact EQ.
Qed.

Lemma nextSince_switchBc_modeEq m m' t i n p :
  nextSince m t i n p -> switchBcStateNet m' i n -> m = m'.
(*Proof: Inudction nextSince, eliminate all non-matching state predicates.*)
Proof.
  (* m and m' are both the next mode, by nextSince_next and switchBc_nextMode_net.*)
  intros NS SB. eapply nextModeNet_unique;
    [exact (nextSince_next _ _ _ _ _ NS) | exact (switchBc_nextMode_net _ _ _ p SB)].
Qed.

Lemma nextSince_ovWait_modeEq m m' t t' x y i n p :
  nextSince m t i n p -> ovWaitStateNet m' t' x y i n -> m = m'.
(*Proof: Inudction nextSince, eliminate all non-matching state predicates.*)
Proof.
  (* m and m' are both the next mode, by nextSince_next and
  ovWait_ovReady_nextMode_net.*)
  intros NS OW. eapply nextModeNet_unique;
    [exact (nextSince_next _ _ _ _ _ NS)
    | exact (proj1 (ovWait_ovReady_nextMode_net i n p) _ _ _ _ OW)].
Qed.

(*If an entity is tfs m, then it is in some tfsState.*)
Theorem tfs_rel_state (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableProtNet n) : tfs m t i n p -> tfsStateNet i n .
Proof.
  intros H.
  induction H as [i0 n0 p0 TS CM | a0 t0 i0 n0 n0' p0 w0 H0 IH TS
    | d0 t0 i0 n0 n0' p0 w0 H0 IH].
  - apply tfsStart_tfs_net. exact TS.
  - exact TS.
  - assert (OS : overlapStateNet i0 n0).
    { destruct IH as [e _ E]. exact (proj1 (proj2 (reachableProtNet_states _ _ _ p0 E))). }
    exact (proj1 (tfsState_del_pres_net _ _ _ _ OS w0) IH).
Qed.

(*The tfs relation is at zero time when in the state tfsStart.*)

(** Two named states of the overlap component of one entity are bisimilar.*)
Lemma overlap_states_bisim_net (X Y : ProcTerm) i n :
  liftEntNet (liftProcEnt (liftOverlap (fun p => p ~p~ X))) i n ->
  liftEntNet (liftProcEnt (liftOverlap (fun p => p ~p~ Y))) i n -> X ~p~ Y.
Proof.
  intros HX HY. net_state_destr HX p1 p2 p3 l h k E.
  lets HY' : liftEntNet_ent HY E. inversion HY' as [q l' h' k' HYp]; subst.
  inversion HYp as [q1 q2 q3 BY]; subst.
  eapply bisim_trans; [apply bisim_symm; exact HX | exact BY].
Qed.

(** A discrete step from tfsStart or tfsNext keeps the current mode: only switchCurr and
tfsCurr write on mCurr.*)
Local Lemma currModeNet_tfsStart_tfsNext_disc m i n n' a :
  reachableProtNet n -> n -NA- a -NA> n' ->
  (tfsStartStateNet i n \/ exists m', tfsNextStateNet m' i n) ->
  currModeNet m i n -> currModeNet m i n'.
Proof.
  intros R S ST [e CE E].
  destruct (link_net_ent_disc_fwd _ _ _ _ _ S E) as [e' [E' [EQ | [b B]]]].
  - subst e'. econstructor; [exact CE | exact E'].
  - econstructor; [ | exact E'].
    destruct (eqDecMode (currModeEnt e) (currModeEnt e')) as [EQ | NE]; [congruence | exfalso].
    destruct (currMode_switch_states_ent _ _ _ (reachableNet_ent _ _ _ _ R E) B NE)
      as [[C _] | [C _]]; pose proof (lenWitness _ _ _ _ C E) as CN;
      destruct ST as [ST | [m' ST]].
    + pose proof (overlap_states_bisim_net tfsStart switchCurr i n ST CN) as BT.
      ovWait_bisim_contra BT.
    + pose proof (overlap_states_bisim_net (tfsNext m') switchCurr i n ST CN) as BT.
      ovWait_bisim_contra BT.
    + pose proof (overlap_states_bisim_net tfsStart tfsCurr i n ST CN) as BT.
      ovWait_bisim_contra BT.
    + pose proof (overlap_states_bisim_net (tfsNext m') tfsCurr i n ST CN) as BT.
      ovWait_bisim_contra BT.
Qed.

(** While an entity is tfs m and in tfsStart or tfsNext, no time has passed since it became
tfs, and its current mode is m: both states are urgent, the one follows the other, and
neither writes on mCurr.*)
Local Lemma tfs_tfsStart_tfsNext_inv m t i n (p : reachableProtNet n) :
  tfs m t i n p -> (tfsStartStateNet i n \/ exists m', tfsNextStateNet m' i n) ->
  currModeNet m i n /\ t = zeroTime.
Proof.
  intros H. induction H as [i0 n0 p0 TS CM | a0 t0 i0 n0 n0' p0 w0 H0 IH TSn
    | d0 t0 i0 n0 n0' p0 w0 H0 IH]; intros S.
  - split; [exact CM | reflexivity].
  - assert (S0 : tfsStartStateNet i0 n0 \/ exists m', tfsNextStateNet m' i0 n0).
    { lets TS0 : tfs_rel_state H0. destruct S as [S | [m' S]].
      - (* tfsStart is entered only from dormant or ovWait, which are no tfs states *)
        net_state_destr TS0 p1 p2 p3 l h k E. net_state_destr S p1' p2' p3' l' h' k' E'.
        destruct (triple_disc_net _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w0 E E')
          as [_ [[EQ | [b B]] _]].
        + subst p2'. left. net_state_intro E. exact S.
        + exfalso. lets PS : reachableProtNet_triple p0 E.
          inversion PS as [q1 q2 q3 BS OS LS]; subst.
          destruct (tfsStart_prev _ _ _ B OS S) as [D | [m1 [e2 [e3 [e4 D]]]]];
            destruct TS0 as [T | m0 T | T | T | T]; red in T;
            try red in D; lets BT : bisim_trans (bisim_symm _ _ D) T; ovWait_bisim_contra BT.
      - destruct TS0 as [e TE E].
        destruct (reachableProtNet_states _ _ _ p0 E) as [_ [OS _]].
        destruct (tfsNext_prev_net _ _ _ _ _ OS S w0) as [S0 | S0];
          [right; exists m'; exact S0 | left; exact S0]. }
    destruct (IH S0) as [CM0 Z]. split; [ | exact Z].
    eapply currModeNet_tfsStart_tfsNext_disc; eassumption.
  - exfalso. destruct S as [S | [m' S]].
    + destruct (reachableProtNet_del_prev _ _ _ _ _ p0 w0 S) as [_ [OS _]].
      eapply tfsStart_urgent_net; [eapply del_pres_bkwd_tfsStart; eassumption | exact w0].
    + destruct (reachableProtNet_del_prev _ _ _ _ _ p0 w0 S) as [_ [OS _]].
      eapply tfsNext_urgent_net; [exact p0 | eapply del_pres_bkwd_tfsNext; eassumption | exact w0].
Qed.

Lemma currModeNet_switch_states n n' a m m' i :
  reachableProtNet n -> n -NA- a -NA> n' -> currModeNet m i n ->
  currModeNet m' i n' -> m <> m' ->
  (switchCurrStateNet i n /\ switchListenStateNet i n') \/
  (tfsCurrStateNet i n /\ tfsBcStateNet i n').
Proof.
  intros R S C C' NE.
  destruct C as [e Ce E]. destruct C' as [e' Ce' E'].
  destruct (link_net_ent_disc _ _ _ _ _ _ S E E') as [EQ | [b B]].
  { subst e'. congruence. }
  subst m m'.
  destruct (currMode_switch_states_ent _ _ _ (reachableNet_ent _ _ _ _ R E) B NE)
    as [[A D] | [A D]]; [left | right];
    (split; [econstructor; [exact A | exact E] | econstructor; [exact D | exact E']]).
Qed.

(*Proof: First of all use a tactic to generate the entities and the entity level
predicates, then do brute force elimination on these using a tactic leaving only
the desirable cases. Finally map the entity level results back up to the network
level using a tactic- netState_auto_tac or some variant?*)

(*tfs and tfsNext state simultaneously mean the mode parameters coincide*)

(* If the nextSince relation holds for some m t then the entity in question
is in a nextSinceState.*)
Theorem nextSince_rel_state (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableProtNet n) : nextSince m t i n p -> nextSinceStateNet i n. 
  (*Induction on nextSince.*)
  intro U. induction U.
  (*The base case follows because ovWaitStateNet m t' x y i n' is a nextSinceStateNet.*)
  netprottrip H1 U q l0 h k.
  dofirst4 econstructor. apply U0. apply U.
  (*The discrete inductive case follows immediately from the definition of nextSince.*)
  assumption.
  (*The delay case follows by applying I.H. to the previous state to get nextSinceStateNet i n*)
  netprottrip IHU U q l h k.
  (*Then we show that delay preserves this state predicate
  (...del_pres_nextSinceState...).*)
  lets DX : net_del_elim U0 w. decompEx4 DX q' l' h' k' DE.
  andflat Q.
  match goal with [PD : _ $||$ _ $||$ _ -PD- _ -PD> _ |- _] => triple_del_inv PD end.
  dofirst3 econstructor. eapply del_pres_nextSinceState.
  apply U1. eassumption. apply Q. Qed.


(*Let's say two entities e1 and e2 are separated by a distance x. If e1 has delivered
message v to radius r t time units ago, and x + 2*Smax*t <= r, then e2 has received v t time
units ago.*)
Theorem delivered_received (n : Network) (v : list BaseValue) (t : Time) (r x : Distance)
  (i j : nat) (p : reachableProtNet n) (l : Position) :
  delivered ([-v, l, r-]) t i n p -> i <> j ->
  distNet i j n x -> x + 2*speedMax*t <= r -> received v t j n p.
  intros. generalize dependent x.
  (*Induction on the proof of delivered.*)
  induction H; intros.
  (*In the base case, we have that n -v_l_r_i!-> n' and t = 0. So our last hypothesis
  becomes x <= r.*)
  simpl in H1. rewrite Rmult_0_r in H2. rewrite Rplus_0_r in H2.
  (*By analysing the transition from n to n', we can see from the semantics
  that this can only happen when all entities within range of entity i input the message,
  and all others ignore.*)
  addHyp (distNet_elim i j n' x H1). decompose [ex] H. clear H. decompose [and] H4.
  clear H4. rename x0 into e1'. rename x1 into e2'.
  addHyp (link_net_ent_disc_bkwd n n' e2' j (([-v, l, r-]) /! i) w H5).
  decompExAnd H3 e2 H4 Q.
  (*By x <= r, our guy is within range. Therefore he inputs.*)
  addHyp (inRange_out_input n n' v l r x i j e2 w H4 H0 H1 H2).
  invertClear H3. invertClear H7.
  (*Therefore, by the base case of received, he receives, with time
  parameter 0, as required.*)
  eapply receivedBase. apply H4. apply H8. apply H3.
  (*In the discrete case of induction, we get that the distance x doesn't change between n and n'*)
  addHyp (disc_pres_distNet_bkwd n n' a i j x w H1).
  (*The goal the follows easily by discrete inductive case of received
  and inductive hypothesis.*)
  constructor. apply (IHdelivered H0 x);assumption.
  (*In the timed case, we have delivered v r t i n p and so we can show
  delivered v r (t + d) i n' p'*)
  remember (reachNetDel n n' d p w) as p'.
  assert (delivered ([-v, l, r-]) (t +dt+ d) i n' p'). rewrite Heqp'. constructor.
  assumption.
  (*Let's call the distance at n' x'. Then we have that dist2d i j n' x' and x' + 2*Smax*(t + d) <= r*)
  rename x into x'.
  (*The latter rearranges to x' + 2*Smax*t + 2*Smax*d <= r.*)
  assert (nonneg (distance x') +
  2 * nonneg speedMax * nonneg (time t) + 2 * nonneg speedMax * pos (delay d)
  <= nonneg (distance r)). rewrite Rmult_assoc in H2. simpl in H2.
  repeat rewrite Rmult_plus_distr_l in H2. rewrite <- Rplus_assoc in H2.
  repeat rewrite <- Rmult_assoc in H2. assumption.
  (*But we can also prove that x <= x' + 2*Smax*d, where dist2d i i' n x.*)
  addHyp (del_link_distNet_bkwd n n' d i j x' w H1). invertClear H5.
  invertClear H6.
  (*Strategically adding 2*Smax*t to each side of the inequality we get
  x + 2*Smax*t <= x' + 2*Smax*t + 2*Smax*d*)
  apply (Rplus_le_compat_r (2*speedMax*t)) in H7.
  (*Now, from a previous result, this is in turn <= r. So x + 2*Smax*t <= r.*)
  assert (x + 2 * speedMax * t <= r). eapply Rle_trans. apply H7.
  eapply Rle_trans;[ |apply H2]. apply Req_le. simpl. ring.
  (*So we have enough information now to show from the I.H. that received v t j n p.*)
  assert (received v t j n p). apply (IHdelivered H0 x); assumption.
  (*And so by the delay constructor of received, we get received v (t + d) i' n p'.*)
  rewrite Heqp'. constructor. assumption.
  (*Note: The intuition here is that e1 and e2 could have been separated by at most
  x + 2*Smax*t t time units ago, due to the separation being x now, the maximum
  relative speed being 2*Smax and the time since the message delivery being t.*) 
  Qed. 

(*The currSince relation for mode m implies that the current mode we are now in is m.*)
Theorem currSince_curr (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableProtNet n) : currSince m t i n p -> currModeNet m i n.
  intros.
  (*Induction on currSince.*)
  induction H.
  (*Base case follows from previous results.*)
  eapply switch_states_mState; try apply w; try assumption. eapply nextSince_next. 
  apply H.
  (*The discrete inductive case is straightforward: the definition of currSince includes in
  it that the currMode is m, so the goal follows immediately.*)
  assumption.
  (*Delay doesn't change the mode state, so I.H. will do.*)
  erewrite <- currModeNet_del_pres. apply IHcurrSince. apply w. 
  Qed.

(*If an entity is tfs t in the state tfsCurrState, then there is some t' such that
the mode transition guard for that entity is t' and the sum of t and t' is at most
trans m.*)

(** Software that offers the switch on mCurr keeps an entity from delaying past the timer of
its mode transition: once the timer runs out, the mode state takes the switch. So a delay
of the entity counts the timer down by exactly the delay.*)
Local Lemma ent_del_mCurrWrite_timer p l h m m' t d e' :
  discActEnabled p (chanMCurrWrite *!) ->
  [|p, l, h, <|m, m', t|>|] -ED- d ->> e' ->
  exists (D : d <= t), mstEnt e' = <|m, m', minusTime t d D|>.
Proof.
  intros DA DEL. inversion DEL as [d0 p0 p' l0 delta h0 h' k0 k' PD HD KD DISP NS]; subst.
  simpl. destruct (Rle_lt_dec d t) as [LE | LT].
  - exists LE. pose proof (cond_pos d) as DP.
    inversion KD; subst.
    + exfalso. simpl in LE. lra.
    + f_equal. apply timeEqR. simpl. ring.
    + exfalso. lra.
  - exfalso. destruct (Req_dec (nonneg (time t)) 0) as [Z | NZ].
    + (* the timer has run out already: the switch is on offer now *)
      assert (TZ : t = zeroTime) by (apply timeEqR; exact Z). subst t.
      destruct (NS (chanMCurrWrite *!)) as [NOW _].
      destruct (NOW DA) as [_ [NM _]]. apply NM. apply mst_tout_mCurr_in.
    + (* the timer runs out during the delay: the switch is on offer then *)
      assert (TP : 0 < nonneg (time t)) by (pose proof (cond_nonneg (time t)); lra).
      set (dt := mkDelay (mkposreal _ TP)).
      assert (SPL : d = dt +d+ minusDelay d t LT) by (apply delayEqR; simpl; ring).
      destruct (timeSplit _ _ _ _ _ PD SPL) as [p1 [PD1 _]].
      destruct (timeSplit_inter _ _ _ _ _ HD SPL) as [h1 [HD1 _]].
      assert (KD1 : <|m, m', t|> -ms- dt -ms> <|m, m', zeroTime|>).
      { apply stepMsDelGuard. apply timeEqR. simpl. ring. }
      destruct (NS (chanMCurrWrite *!)) as [_ LATER].
      assert (LTd : pos (delay dt) < pos (delay d)) by (simpl; exact LT).
      lets NOW1 : LATER LTd PD1 HD1 KD1.
      destruct (NOW1 (persistence _ _ _ _ PD1 DA)) as [_ [NM _]].
      apply NM. apply mst_tout_mCurr_in.
Qed.

(** A delay of an entity in tfsCurr counts its mode transition timer down by the delay, and
cannot be longer than the timer.*)
Local Lemma transGuard_tfsCurr_del n n' d t i :
  n -ND- d -ND> n' -> tfsCurrStateNet i n -> transGuard t i n ->
  exists (D : d <= t), transGuard (minusTime t d D) i n'.
Proof.
  intros ND TC TG. destruct TG as [p l h m m' E].
  destruct (link_net_ent_del_fwd _ _ _ _ _ ND E) as [e' [E' DEL]].
  assert (DA : discActEnabled p (chanMCurrWrite *!)).
  { lets TCe : liftEntNet_ent TC E. inversion TCe as [p0 l0 h0 k0 TP]; subst.
    inversion TP as [p1 p2 p3 TS]; subst. dae_overlap. apply tfsCurr_mCurr_out. exact TS. }
  destruct (ent_del_mCurrWrite_timer _ _ _ _ _ _ _ _ DA DEL) as [D K].
  exists D. destruct e' as [p' l' h' k']. simpl in K. subst k'. econstructor. exact E'.
Qed.

Theorem tfs_transGuard (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableProtNet n) : 
  tfsCurrStateNet i n -> tfs m t i n p ->
  exists t', transGuard t' i n /\ t + t' <= trans m.
Proof.
  intros TC H. revert TC.
  induction H as [i0 n0 p0 TS CM | a0 t0 i0 n0 n0' p0 w0 H0 IH TSn
    | d0 t0 i0 n0 n0' p0 w0 H0 IH]; intros TC.
  - exfalso. eapply state_disj_tfsCurr_start; eassumption.
  - destruct (tfsCurrNet_dec i0 n0) as [TC0 | NTC0].
    + (* in tfsCurr already: only its own switch into tfsBc would change the mode state *)
      destruct (IH TC0) as [t' [TG LE]]. exists t'. split; [ | exact LE].
      destruct TG as [q l h m1 m2 E].
      destruct (mState_disc_pres _ _ _ _ _ w0 (minet _ _ _ _ _ _ E)) as [k' MS'].
      destruct (eqDecModeState (<|m1, m2, t'|>) k') as [EQ | NE].
      * subst k'. destruct MS' as [q' l' h' E']. econstructor. exact E'.
      * exfalso.
        destruct (mState_switch_states _ _ _ _ _ _ p0 (unstbl m1 m2 t') NE w0
          (minet _ _ _ _ _ _ E) MS') as [[_ B] | [[_ B] | [[_ B] | [m0 [_ B]]]]].
        -- exact (state_disj_tfsCurr_bc _ _ TC B).
        -- exact (state_disj_tfsCurr_switchListen _ _ TC B).
        -- exact (state_disj_tfsCurr_dormant _ _ TC B).
        -- exact (state_disj_tfsCurr_tfsNext _ _ _ TC B).
    + (* just in from tfsNext, which wrote the fail-safe successor of the current mode *)
      destruct (tfsCurrStateNet_bktrk_net _ _ _ _ p0 TC w0)
        as [TC0 | [m1 [mF [pr [TN [FS MS]]]]]]; [contradiction | ].
      destruct (tfs_tfsStart_tfsNext_inv _ _ _ _ _ H0 (or_intror (ex_intro _ m1 TN)))
        as [CM Z].
      assert (CM' : currModeNet m i0 n0').
      { eapply currModeNet_tfsStart_tfsNext_disc;
          [exact p0 | exact w0 | right; exists m1; exact TN | exact CM]. }
      assert (EQ : m1 = m).
      { destruct MS as [q' l' h' E']. lets C : liftEntNet_ent CM' E'. simpl in C. exact C. }
      subst m1 t0. exists (modeTransTime m mF pr). split.
      * eapply transGuard_intro. exact MS.
      * simpl. pose proof (modeTransTime_bound m mF pr FS). lra.
  - (* a delay: in tfsCurr before it, and the timer goes down as the time goes up *)
    destruct (reachableProtNet_del_prev _ _ _ _ _ p0 w0 TC) as [_ [OS _]].
    assert (TC0 : tfsCurrStateNet i0 n0)
      by (apply (tfsCurrState_del_pres_net _ _ _ _ OS w0); exact TC).
    destruct (IH TC0) as [t' [TG LE]].
    destruct (transGuard_tfsCurr_del _ _ _ _ _ w0 TC0 TG) as [D TG'].
    exists (minusTime t' d0 D). split; [exact TG' | ]. simpl. simpl in LE. lra.
Qed.
(**Proof: Induction on tfs.*)

  
(*If an entity is tfs m for a time of t, then this t is bounded from above by trans m.*)

Theorem tfs_bound (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableProtNet n) : tfs m t i n p -> t <= trans m.
Proof.
  intros H.
  induction H as [i0 n0 p0 TS0 CM0 | a0 t0 i0 n0 n0' p0 w0 H0 IH0 TSn
    | d0 t0 i0 n0 n0' p0 w0 H0 IH0].
  - simpl. apply cond_nonneg.
  - exact IH0.
  - (* a delay: of the tfs states, only tfsCurr lets time pass, and only while its timer
       lasts *)
    lets TS : tfs_rel_state H0. apply tfsState_elim_net in TS.
    destruct TS as [S | [[m2 S] | [S | [S | S]]]].
    + exfalso. eapply tfsStart_urgent_net; eassumption.
    + exfalso. eapply tfsNext_urgent_net; eassumption.
    + assert (OS : overlapStateNet i0 n0)
        by (destruct S as [e _ EIN]; exact (proj1 (proj2 (reachableProtNet_states _ _ _ p0 EIN)))).
      assert (TC' : tfsCurrStateNet i0 n0')
        by (apply (proj1 (tfsCurrState_del_pres_net _ _ _ _ OS w0)); exact S).
      destruct (tfs_transGuard _ _ _ _ _ TC' (tfsDel m d0 t0 i0 n0 n0' p0 w0 H0))
        as [t' [_ LE]].
      pose proof (cond_nonneg (time t')). simpl in LE |- *. lra.
    + exfalso. destruct S as [e SE EIN].
      destruct (del_net_ent e i0 n0 n0' d0 EIN w0) as [e' ED].
      destruct (reachableProtNet_states _ _ _ p0 EIN) as [BS _].
      eapply tfsBc_urgent; [exact (liftEntNet_ent _ _ _ _ BS EIN) | exact SE | exact ED].
    + (* the listener of a delaying entity is listening, and takes tfsListen's unpause *)
      exfalso. destruct S as [e SE EIN].
      lets LN : del_listening_net p0 w0 EIN. lets LS : liftEntNet_ent LN EIN.
      destruct (del_net_ent e i0 n0 n0' d0 EIN w0) as [e' ED].
      destruct e' as [p' l' h' k'].
      ent_state_destr SE p1 p2 p3 l h k. ent_state_comp LS.
      lets DP : link_ent_soft_del ED.
      triple_del_sync_not DP (tfsListen_unpause_out _ SE) (listening_unpause_in _ LS).
Qed.



(*If v is timed out and outgoing from the entity i at position l, and the parent network makes
a discrete transition, then in the resultant network, v is either still timed out and outgoing
or it has just been delivered from l in this instant.*)
Theorem outgoing_timeout_disc (n n' : Network) (a : ActDiscNet) (i : nat)
  (p : reachableProtNet n) (w : n -NA- a -NA> n') (v : list BaseValue) (l : Position) :
  inPosNet l i n -> outgoing v zeroTime i n ->
  outgoing v zeroTime i n' \/
  exists r, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
Proof.
  intros IP OG.
  (*The only case where something is in the output list of an interface and not in the
  output list of the derivative is where the action linking the states is a broadcast
  of the message in question, which gives us delivered with timestamp 0 i.e. the RHS.
  For a of type tau, input or ignore, outgoing is preserved, hence the LHS.*)
  destruct (outgoing_disc _ _ _ _ _ _ _ w IP OG) as [OG' | [_ [r EQ]]].
  - left. exact OG'.
  - right. exists r. subst a. apply deliveredBase with (t := zeroTime).
Qed.
(**Proof: In steps above*)

(*AMALGAMATE WITH OTHERS- cull repetitions?*)
(* begin helpers for notifAbortPathNet_urgent *)
Lemma notifAbortPathNet_urgent_rangeBad_in m m0 p :
  rangeBadState m p -> discActEnabled p (chanMCurrRead ;? [baseMode m0]).
Proof. activation_tac. Qed.

Lemma notifAbortPathNet_urgent_currOK_in m m0 p :
  currOKState m p -> discActEnabled p (chanMNextRead ;? [baseMode m0]).
Proof. activation_tac. Qed.

(** An entity whose listener is in the rangeBad state can always read the
current mode from its mode state, so it cannot delay. No reachability needed.*)
Lemma notifAbortPathNet_urgent_rangeBad_ent m p l h k e' d :
  rangeBadStateProt m p -> [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros RB ED. inversion RB as [p1 p2 p3 RB3 EQ]; subst.
  noSyncNow_tac.
  destruct (NS (chanMCurrRead ;? [baseMode (currModeMState k)])) as [_ [DM _]].
  - dae_listener.
    exact (notifAbortPathNet_urgent_rangeBad_in m (currModeMState k) p3 RB3).
  - apply DM. exact (modeState_curr_enabled k).
Qed.

(** An entity whose listener is in the currOK state while its mode state has
a next mode m' can read m' on mNext, so it cannot delay.*)
Lemma notifAbortPathNet_urgent_currOK_ent m m' p l h k e' d :
  currOKStateProt m p -> nextModeMState k = Some m' ->
  [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros CO NM ED. inversion CO as [p1 p2 p3 CO3 EQ]; subst.
  noSyncNow_tac.
  destruct (NS (chanMNextRead ;? [baseMode m'])) as [_ [DM _]].
  - dae_listener.
    exact (notifAbortPathNet_urgent_currOK_in m m' p3 CO3).
  - apply DM. destruct k as [m0 | m0 m1 t0]; simpl in NM; inversion NM; subst.
    econstructor. apply stepMsOutNext.
Qed.

Lemma notifAbortPathNet_urgent_ent e e' d :
  reachableProtEnt e -> notifAbortPathEnt e -> e -ED- d ->> e' -> False.
Proof.
  intros RE NA ED.
  inversion NA as [p l h k m m' RB CM NE NM | p l h k m' CO NM | p l h k AO]; subst.
  - eapply notifAbortPathNet_urgent_rangeBad_ent; eassumption.
  - eapply notifAbortPathNet_urgent_currOK_ent; eassumption.
  - eapply abortOvlpStateEnt_urgent; [exact RE | econstructor; exact AO | exact ED].
Qed.
(* end helpers *)

Lemma notifAbortPathNet_urgent (i : nat) (n n' : Network) (d : Delay) :
  reachableProtNet n -> notifAbortPathNet i n -> n -ND- d -ND> n' -> False.
Proof.
  intros RN NA W.
  destruct NA as [e NE EIN].
  destruct (del_net_ent e i n n' d EIN W) as [e' ED].
  eapply notifAbortPathNet_urgent_ent;
    [eapply reachable_net_ent; eassumption | exact NE | exact ED].
Qed.
(**Proof: lift from...EA::urgency... #urgent-path*)

Lemma notifBadPathNet_urgent i n n' d :
  reachableProtNet n -> notifBadPathNet i n -> n -ND- d -ND> n' -> False.
Proof.
  (*A reachable entity that can delay is listening (del_listening), and the listener is in
  rangeBad or badOvlp instead.*)
  intros RN NB W. destruct NB as [e NE EIN].
  destruct (del_net_ent e i n n' d EIN W) as [e' ED].
  lets LS : del_listening (reachable_net_ent _ _ _ RN EIN) ED.
  inversion NE as [p l h k m RB CM | p l h k BO]; subst; ent_state_comp LS.
  - inversion RB as [? ? ? X]; subst. ov_disj LS X.
  - inversion BO as [? ? ? X]; subst. ov_disj LS X.
Qed.
(**Proof: Follows from urgency results from all underlying component states.
Urgency holds in each one because there is always a synch possible with the
mode state or the overlap component. #urgent-path*)

Lemma msgBadPathNet_urgent (n n' : Network) (d : Delay) (i : nat) :
  reachableProtNet n -> msgBadPathNet i n -> n -ND- d -ND> n' -> False.
Proof.
  (*Each state of the path is urgent: gotMsg reads the position, gotRange reads the current
  mode, both always on offer, and badOvlp is on the notification bad path too.*)
  intros RN MB DEL. destruct MB as [e ME EI].
  destruct (del_net_ent e i n n' d EI DEL) as [e' ED].
  inversion ME as [p l h k m'' m l' GM CM PI | p l h k m'' m r GR CM PI | p l h k BO]; subst.
  - eapply gotMsgStateEnt_urgent; [ | exact ED]. constructor. exact GM.
  - eapply gotRangeStateEnt_urgent; [ | exact ED]. constructor. exact GR.
  - eapply notifBadPathNet_urgent; [exact RN | | exact DEL].
    econstructor; [ | exact EI]. apply nbpBad. exact BO.
Qed.
(**Proof: Lift urgency from EA urgency result. #urgent-path*)

(* begin helpers for msgAbort_paused_disj_net *)
Lemma msgAbort_paused_disj_net_unp q :
  pausedState q -> exists q', q -PA- chanUnpause *? -PA> q'.
Proof.
  intro P.
  assert (exists q', paused -PA- chanUnpause *? -PA> q') as [q0 TR].
  { eexists. unfold paused. constructor. typed_vals. }
  apply ComhCoq.lang.ProcEquiv.bisim_symm in P.
  exact (bisim_disc_match _ _ _ _ P TR).
Qed.

Ltac msgAbort_paused_disj_net_inv :=
  repeat (match goal with V : _ -PA- _ -PA> _ |- _ => inversion V; subst; clear V end).
(* end helpers *)

Lemma msgAbort_paused_disj_net (i : nat) (n : Network) :
  msgAbortPathNet i n -> pausedStateNet i n -> False.
Proof.
  intros U V. destruct U as [e E1 E2]. destruct V as [e' E1' E2'].
  assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
  inversion E1' as [p l h k P]; subst.
  inversion P as [p1 p2 p3 P3]; subst.
  destruct (msgAbort_paused_disj_net_unp _ P3) as [q' TQ].
  inversion E1; subst.
  - match goal with H : gotMsgStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : gotMsgState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold gotMsg in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : gotRangeStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : gotRangeState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold gotRange in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : currCompStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : currCompState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold currComp in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : abortOvlpStateProt _ |- _ => inversion H; subst end.
    match goal with H : abortOvlpState _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold abortOvlp in TR. msgAbort_paused_disj_net_inv.
Qed.

(** No entity of a network is both on the message bad path and paused.*)
Lemma msgBad_paused_disj_net (i : nat) (n : Network) :
  msgBadPathNet i n -> pausedStateNet i n -> False.
Proof.
  intros U V. destruct U as [e E1 E2]. destruct V as [e' E1' E2'].
  assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
  inversion E1' as [p l h k P]; subst.
  inversion P as [p1 p2 p3 P3]; subst.
  destruct (msgAbort_paused_disj_net_unp _ P3) as [q' TQ].
  inversion E1; subst.
  - match goal with H : gotMsgStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : gotMsgState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold gotMsg in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : gotRangeStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : gotRangeState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold gotRange in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : badOvlpStateProt _ |- _ => inversion H; subst end.
    match goal with H : badOvlpState _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold badOvlp in TR. msgAbort_paused_disj_net_inv.
Qed.

(** An entity that leaves the tfs states in a discrete step was not currSince in a mode
that is not fail safe: while its mode is not fail safe, a discrete step keeps it in the tfs
states (tfs_currMode_disc_pres). A fail-safe mode may be its own fail-safe successor, so an
entity in such a mode can run through the tfs states and out again without its mode
changing, which is why the hypothesis is needed.*)
Lemma tfsState_not_currSince (m : Mode) (t : Time) (i : nat) (n n' : Network)
  (p : reachableProtNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
  ~ failSafe m -> tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p.
Proof.
  intros NFS TS NTS CS. apply NTS.
  eapply (tfs_currMode_disc_pres n n' a i m); [exact p | exact w | | exact NFS | exact TS].
  eapply currSince_curr. exact CS.
Qed.

(** badOvlp only outputs on bad.*)
Lemma badOvlp_step_act p p' b : badOvlpState p -> p -PA- b -PA> p' -> b = chanBad ;! [].
Proof.
  intros A T. destruct (bisim_step_disc _ _ _ _ A T) as [q [TQ _]]. unfold badOvlp in TQ.
  inversion TQ; subst. match goal with [E : evalExpLists [] _ |- _] => inversion E end.
  reflexivity.
Qed.

(** The broadcast component never inputs on bad.*)
Local Lemma bc_bad_in_not p p' : p -PA- chanBad *? -PA> p' -> broadcastState p -> False.
Proof. intros TR S. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra. Qed.

(** The overlap component enters a tfs state when it inputs on bad.*)
Local Lemma ovlp_bad_in_tfsState p p' :
  p -PA- chanBad *? -PA> p' -> overlapState p -> tfsState p'.
Proof.
  intros TR OS. destruct (overlapState_shape _ OS)
    as [B | v B | v e2 e3 e4 B | v1 e2 v3 B | m0 B | B | B | B | B | v B | B | B | B];
    try solve [exfalso; prot_outProc_in_not_contra];
    destruct (bisim_step_disc _ _ _ _ B TR) as [q' [TQ BQ]];
    prot_outProc_in_not_body; invert_disc_prefixes;
    let close := (red; (eapply bisim_trans; [exact BQ | ]); apply app_bisim_nil; reflexivity) in
    first [solve [apply tfsStaSt; close] | solve [apply tfsCurSt; close]
      | solve [apply tfsLisSt; close]].
Qed.

(** In a step of a reachable entity in which the listener moves by an output on a channel
the entity does not offer, the broadcast or the overlap component inputs on that channel, and
the mode state stays.*)
Lemma listener_internal_out_sync_ent p1 p2 p3 p1' p2' p3' l l' h h' k k' a c :
  protocolState (p1 $||$ p2 $||$ p3) ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- a ->> [|p1' $||$ p2' $||$ p3', l', h', k'|] ->
  chanDir c = None -> (forall b, p3 -PA- b -PA> p3' -> b = c ;! []) -> p3 <> p3' ->
  (p1 -PA- c ;? [] -PA> p1' \/ p2 -PA- c ;? [] -PA> p2') /\ k' = k.
Proof.
  intros PS S CD ACT NE.
  inversion S; subst; try (exfalso; apply NE; reflexivity).
  (* a silent step of the software: a synchronisation *)
  1: split; [ | reflexivity];
     match goal with [T : _ $||$ _ $||$ _ -PA- tauAct -PA> _ |- _] =>
       destruct (link_reach_triple_tau _ _ _ _ _ _ T PS) as [c0 [v0 Q]] end;
     decompose [or and] Q; clear Q; subst;
     try (exfalso; apply NE; reflexivity);
     match goal with [N : ?x <> ?x', T3 : ?x -PA- _ -PA> ?x' |- _] =>
       pose proof (ACT _ T3) as X; first [discriminate X | inversion X; subst] end;
     first [left; assumption | right; assumption].
  (* a step of the software on one of the entity's channels: one component moves *)
  all: exfalso;
    match goal with [T : _ $||$ _ $||$ _ -PA- _ -PA> _ |- _] => triple_disc_nonTau T end;
    try (apply NE; reflexivity);
    match goal with [N : ?x <> ?x', T3 : ?x -PA- _ -PA> ?x' |- _] =>
      pose proof (ACT _ T3) as X; first [discriminate X | inversion X; subst;
        discriminate CD] end.
Qed.

Lemma msgBad_disc_net (n n' : Network) (a : ActDiscNet) (i : nat)
  (p : reachableProtNet n) (w : n -NA- a -NA> n') :
  msgBadPathNet i n -> msgBadPathNet i n' \/ tfsStateNet i n'.
Proof.
  intros U.
  destruct U as [e E I].
  destruct (link_net_ent_disc_fwd n n' e i a w I) as [e' [I' [EQ | [b ST]]]].
  { subst e'. left. econstructor; eassumption. }
  assert (R : reachableProtEnt e) by (eapply reachable_net_ent; eassumption).
  destruct e as [p0 l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p0.
  destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ ST)
    as [p1' [p2' [p3' [l' [h' [k' [EQ' [W1 [W2 W3]]]]]]]]].
  subst e'.
  pose proof (stepEnt_disc_pres_pos _ _ _ ST) as LE. simpl in LE. subst l'.
  destruct (eqDecProcTerm p3 p3') as [E3 | N3].
  - (* the listener stays: the path holds again unless the current mode changed, which only
       the overlap component's switch does, from switchCurr, where the listener is paused, or
       from tfsCurr into tfsBc *)
    subst p3'.
    destruct (eqDecMode (currModeMState k) (currModeMState k')) as [KE | KN].
    + left. econstructor; [ | exact I']. inversion E; subst.
      * match goal with [H : gotMsgStateProt _ _ _ |- _] =>
          inversion H as [? ? ? G]; subst end.
        eapply mbpMsg; [constructor; exact G | symmetry; exact KE | eassumption].
      * match goal with [H : gotRangeStateProt _ _ _ |- _] =>
          inversion H as [? ? ? G]; subst end.
        eapply mbpRng; [constructor; exact G | symmetry; exact KE | eassumption].
      * match goal with [H : badOvlpStateProt _ |- _] => inversion H as [? ? ? BO]; subst end.
        apply mbpBad. constructor. exact BO.
    + destruct (currMode_switch_states_ent _ _ _ R ST KN) as [[SC _] | [_ TB]].
      * exfalso. eapply msgBad_paused_disj_net; [econstructor; [exact E | exact I] | ].
        apply (proj2 (paused_switch_net n i p)). econstructor; [ | exact I].
        apply switchCurr_switch_ent. exact SC.
      * right. econstructor; [ | exact I']. ent_state_comp TB.
        constructor. constructor. apply tfsBcSt. exact TB.
  - (* the listener steps *)
    destruct W3 as [E3 | [b3 T3]]; [contradiction | ].
    inversion E; subst.
    + (* gotMsg: it reads the entity's position, into gotRange with the range the path
         tests *)
      match goal with [H : gotMsgStateProt _ _ _ |- _] => inversion H as [? ? ? G]; subst end.
      assert (ACT : forall c, p3 -PA- c -PA> p3' -> entChanAct c).
      { intros c T. destruct (gotMsg_next_act _ _ _ _ _ T G) as [v [EC _]].
        subst c. left. reflexivity. }
      destruct (triple_disc_ent_chan 2 R ST eq_refl eq_refl ACT) as [E3 | ST3];
        [contradiction | ].
      destruct (ent_disc_proc_read _ _ _ _ _ _ _ _ _ ST3) as [E3 | [c [T [RP _]]]];
        [contradiction | ].
      destruct (gotMsg_next_act _ _ _ _ _ T G) as [v [EC GR]].
      destruct (RP v EC) as [EV KE]. subst v k'.
      left. econstructor; [ | exact I'].
      eapply mbpRng; [constructor; exact GR | reflexivity | eassumption].
    + (* gotRange: it reads the current mode, which the message threatens, into badOvlp *)
      match goal with [H : gotRangeStateProt _ _ _ |- _] => inversion H as [? ? ? G]; subst end.
      assert (ACT : forall c, p3 -PA- c -PA> p3' -> entChanAct c).
      { intros c T. destruct (gotRange_next_act _ _ _ _ _ T G) as [v [EC _]].
        subst c. left. reflexivity. }
      destruct (triple_disc_ent_chan 2 R ST eq_refl eq_refl ACT) as [E3 | ST3];
        [contradiction | ].
      destruct (ent_disc_proc_read _ _ _ _ _ _ _ _ _ ST3) as [E3 | [c [T [_ [RC _]]]]];
        [contradiction | ].
      destruct (gotRange_next_act _ _ _ _ _ T G) as [v [EC CP]].
      destruct (RC v EC) as [EV KE]. subst v k'.
      left. econstructor; [ | exact I'].
      apply mbpBad. constructor. eapply currPincCheck_cond_true; [eassumption | exact CP].
    + (* badOvlp: it outputs on bad, which only the overlap component takes, into a tfs
         state *)
      match goal with [H : badOvlpStateProt _ |- _] => inversion H as [? ? ? BO]; subst end.
      right. econstructor; [ | exact I']. constructor. constructor.
      destruct (listener_internal_out_sync_ent _ _ _ _ _ _ _ _ _ _ _ _ _ chanBad PS ST
        eq_refl (fun b B => badOvlp_step_act _ _ _ BO B) N3) as [[T1 | T2] _].
      * exfalso. eapply bc_bad_in_not; eassumption.
      * eapply ovlp_bad_in_tfsState; eassumption.
Qed.
(**Proof: Decompose msgBadPath. For all cases but one, fwd-tracking gives that either the state is preserved or the next state is also on the bad path, which is the LHS. The only exception is the badOvlp state, in which case the future may be the listening state. In this case though, fwd-tracking gives that the transition was an output on bad. Now, this must be matched in order for a synch to occur, and the only possible match is from the overlap component. There are 3 states in which this listens on bad. We can eliminate tfsListen and tfsCurr because they would imply that the entity is alredy tfs, which contradicts the assumption that it was on the msgBadPath: the definition of msgBadPath dictates that an entity is not tfs. Thus the remaining case is the transition from ovWait to tfsStart, giving the base case for tfs, which is the RHS exactly.*)

(** switchListen is no tfs state.*)
Local Lemma switchListen_tfsState_disj p : switchListenState p -> tfsState p -> False.
Proof.
  intros A T. destruct T as [B | m B | B | B | B];
    unfold switchListenState, tfsStartState, tfsNextState, tfsCurrState, tfsBcState,
      tfsListenState in *;
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ A) B) as BT;
    prot_outProc_in_not_body; clean_proc_hyp BT; refute_by_chan BT.
Qed.

(** An entity in a tfs state other than tfsStart after a discrete step was in a tfs state
before it.*)
Local Lemma tfsState_disc_bkwd n n' a i : reachableProtNet n -> n -NA- a -NA> n' ->
  tfsStateNet i n' -> ~ tfsStartStateNet i n' -> tfsStateNet i n.
Proof.
  intros RN S TS NT. destruct TS as [e' TE E'].
  destruct (link_net_ent_disc_bkwd _ _ _ _ _ S E') as [e [E [EQ | [b B]]]].
  - subst e. econstructor; [exact TE | exact E].
  - destruct e as [p l h k]. lets PS : reachableProtNet_triple RN E.
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    destruct e' as [p' l' h' k'].
    inversion TE as [q l0 h0 k0 TP]; subst. inversion TP as [q1 q2 q3 T2]; subst.
    lets T : triple_disc_ent B. destruct T as [_ [[EQ2 | [c C]] _]].
    + subst q2. econstructor; [ | exact E]. constructor. constructor. exact T2.
    + econstructor; [ | exact E]. constructor. constructor.
      destruct T2 as [A | mt A | A | A | A].
      * exfalso. apply NT. econstructor; [ | exact E']. constructor. constructor. exact A.
      * destruct (tfsNext_prev _ _ _ _ C OS A) as [X | X];
          [apply tfsStaSt | eapply tfsNexSt]; exact X.
      * destruct (tfsCurr_prev _ _ _ C OS A) as [X | [m1 X]];
          [apply tfsCurSt | eapply tfsNexSt]; exact X.
      * apply tfsCurSt. exact (tfsBc_prev _ _ _ C OS A).
      * destruct (tfsListen_prev _ _ _ C OS A) as [X | X];
          [apply tfsLisSt | apply tfsBcSt]; exact X.
Qed.

(** An entity in a tfs state, in a current mode m that is not fail safe, is tfs m for some
time.*)
Lemma tfsState_tfs_exists (n : Network) (p : reachableProtNet n) (m : Mode) (i : nat) :
  tfsStateNet i n -> currModeNet m i n -> ~ failSafe m -> exists t, tfs m t i n p.
Proof.
  induction p as [n I | n n' a p IH w | n n' d p IH w]; intros TS CM NFS.
  - (* no tfs state is initial *)
    exfalso. destruct TS as [e TE E]. lets IE : initialNet_ent I E. inversion IE; subst.
    inversion TE as [q l0 h0 k0 TP]; subst. unfold procProtocol in TP.
    inversion TP as [q1 q2 q3 T2]; subst.
    destruct T2 as [B | mt B | B | B | B];
      unfold tfsStartState, tfsNextState, tfsCurrState, tfsBcState, tfsListenState in *;
      pose proof (bisim_symm _ _ B) as BT; prot_outProc_in_not_body; clean_proc_hyp BT;
      refute_by_chan BT.
  - (* tfsStart is the base of tfs; any other tfs state was a tfs state before the step, in
       the same mode, since only tfsCurr into tfsBc changes it, into a fail-safe mode *)
    destruct (Classical_Prop.classic (tfsStartStateNet i n')) as [TSt | NT].
    + exists zeroTime. apply tfsBase; assumption.
    + lets TSn : tfsState_disc_bkwd p w TS NT.
      destruct (currMode_pres_bkwd _ _ _ _ _ w CM) as [m1 CM1].
      destruct (eqDecMode m1 m) as [EM | NE].
      * subst m1. destruct (IH TSn CM1 NFS) as [t T]. exists t. apply tfsDisc; assumption.
      * exfalso.
        destruct (currModeNet_switch_states _ _ _ _ _ _ p w CM1 CM NE) as [[_ SL] | [_ TB]].
        -- destruct SL as [e SE E]. destruct TS as [e' TE E'].
           pose proof (entInNetUnique _ _ _ _ E E') as EQ. subst e'.
           inversion SE as [q l0 h0 k0 SP]; subst. inversion SP as [q1 q2 q3 S2]; subst.
           inversion TE as [q l1 h1 k1 TP]; subst. inversion TP as [r1 r2 r3 T2]; subst.
           eapply switchListen_tfsState_disj; eassumption.
        -- apply NFS. destruct TB as [e TBe E]. lets CMe : liftEntNet_ent CM E.
           simpl in CMe. rewrite <- CMe.
           eapply tfsBc_failSafe; [ | exact TBe].
           exact (reachable_net_ent _ _ _ (reachNetDisc n n' a p w) E).
  - (* a delay keeps the tfs state and the mode *)
    pose proof TS as TS0. destruct TS0 as [e' TE E'].
    destruct (link_net_ent_del_bkwd _ _ _ _ _ w E') as [e [E _]].
    destruct (reachableProtNet_states _ _ _ p E) as [_ [OS _]].
    pose proof (proj2 (tfsState_del_pres_net n n' i d OS w) TS) as TSn.
    pose proof (proj2 (currModeNet_del_pres n n' d m i w) CM) as CMn.
    destruct (IH TSn CMn NFS) as [t T]. exists (t +dt+ d). apply tfsDel. exact T.
Qed.

(** No overlap component is both init and in a nextSince state.*)
Local Lemma init_nextSinceState_not (m : Mode) (q : ProcTerm) :
  initState m q -> nextSinceState q -> False.
Proof.
  intros I NS.
  assert (S : exists q', init m -PA- chanMCurrRead ;? [baseMode m] -PA> q')
    by (eexists; unfold init; apply stepDpIn; typed_vals).
  destruct S as [q' S].
  destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ I) S) as [r [R _]].
  destruct NS as [m' t x y H | m' t l H | m' H | m' H];
    destruct (bisim_disc_match _ _ _ _ H R) as [r2 R2];
    [unfold ovWait in R2 | unfold ovReady in R2 | unfold switchBc in R2 | unfold switchCurr in R2];
    invert_disc_prefixes.
Qed.

(** No entity of a network has its overlap component both init and in a nextSince state.*)
Lemma init_nextSince_net_not m i n :
  initStateNet m i n -> nextSinceStateNet i n -> False.
Proof.
  intros I NS. net_state_destr I p1 p2 p3 l h k E. net_state_ent NS E.
  exact (init_nextSinceState_not _ _ I NS).
Qed.

Lemma ovWait_nextSince_time (n : Network) (m : Mode) (x y t t1: Time) (i : nat)
  (p : reachableProtNet n) :
  ovWaitStateNet m t x y i n -> nextSince m t1 i n p -> period m - y <= t1.
(**Proof: Induction on next since. The base case gives that y = period m,
so the LHS of the inequality is 0 and trivially true. For the discrete
inductive case, neither t1 nor y changes, and so the I.H. suffices.
For the timed inductive case, y decreases and t1 increases proportionally.
Hence both sides of the inequality increase by the same amount, which can be
cancelled, and then the I.H. is applicable.*)
Proof.
  intros OW NS. revert t x y OW.
  induction NS as [a i0 n0 n0' p0 w l t0 t' x0 y0 PE OR OW0
    | a t2 i0 n0 n0' p0 w NS IH NSS | d t2 i0 n0 n0' p0 w NS IH]; intros tt xx yy OW.
  - (* the broadcast that starts nextSince sets the position timer to the period *)
    destruct (ovReady_wait_track_net _ _ _ _ _ _ _ _ _ _ _ OR OW w) as [_ EY].
    subst yy. simpl. lra.
  - (* back to the state before the step *)
    destruct (ovWait_prev_net _ _ _ _ _ _ _ _ p0 OW w) as [OWN | [[t3 [l3 [_ [_ EY]]]] | IS]].
    + exact (IH _ _ _ OWN).
    + subst yy. pose proof (cond_nonneg (time t2)). lra.
    + exfalso. eapply init_nextSince_net_not; [exact IS | ].
      eapply nextSince_rel_state. exact NS.
  - (* back across the delay: the position timer was longer by the delay *)
    pose proof (proj1 (proj2 (reachableProtNet_del_prev _ _ _ _ _ p0 w OW))) as OS.
    destruct (ovWait_del_bkwd_net _ _ _ _ _ _ _ _ OS w OW) as [x1 OW1].
    pose proof (IH _ _ _ OW1) as IH1. simpl in *. lra.
Qed.

(*The mode parameter of ovWait is the same as that of the nextSince relation if both hold.*)
Lemma nextSince_ovWait_modes_eq (n : Network) (m1 m2 : Mode) (t t1 x y : Time)
  (i : nat) (p : reachableProtNet n) :
  ovWaitStateNet m1 t x y i n -> nextSince m2 t1 i n p -> m1 = m2.
Proof.
  intros OW NS. symmetry. eapply nextSince_ovWait_modeEq; eassumption.
Qed.
(**Proof: Generalise the statement to include a similar statement about ovReadyState, then proceed by induction on nextSince. Back tracking
shows that ovReadySate and ovWaitState are predecessors to each other and so the I.H. carries forward. The base case follows directly from the
definition of nextSince.*)

(** A step of the broadcast component into a wait wakes it, with its timer zero, or is the
broadcast of bcReady, which sets the timer to the period.*)
Local Lemma bcWait_prev (p p' : ProcTerm) (b : DiscAct) (m : Mode) (x : Time) :
  p -PA- b -PA> p' -> broadcastState p -> bcWaitState m x p' ->
  x = zeroTime \/ (exists l, bcReadyState m l p /\ x = period m /\
    b = chanOutProc ;! [baseMode m, basePosition l]).
Proof.
  intros T BS W. red in W. pose proof T as T0.
  destruct (broadcastState_shape _ BS) as [H | m0 e H | m0 l0 H];
    shape_step_pre B;
    change (p' ~p~ bcWait m x) in W.
  - (* sleeping wakes *)
    unfold_app_hyp B. change (p' ~p~ bcWait m0 zeroTime) in B.
    left. destruct (bcWait_bisim_inj _ _ _ _ (bisim_trans _ _ _ (bisim_symm _ _ B) W))
      as [_ E]. symmetry. exact E.
  - (* sleeping stays asleep *)
    exfalso. apply (sleeping_not_bcWait m x). eapply bisim_trans; [ | exact W].
    apply bisim_symm. eapply bisim_trans; [exact B | ]. apply app_bisim_nil. reflexivity.
  - (* a wait goes to sleep *)
    exfalso. apply (sleeping_not_bcWait m x). eapply bisim_trans; [ | exact W].
    apply bisim_symm. eapply bisim_trans; [exact B | ]. apply app_bisim_nil. reflexivity.
  - (* a wait reads its position *)
    exfalso. unfold_app_hyp B.
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ B) W) as BT.
    unfold bcWait in BT. refute_by_chan BT.
  - (* a wait is woken again *)
    unfold_app_hyp B. change (p' ~p~ bcWait m1 zeroTime) in B.
    left. destruct (bcWait_bisim_inj _ _ _ _ (bisim_trans _ _ _ (bisim_symm _ _ B) W))
      as [_ E]. symmetry. exact E.
  - (* bcReady broadcasts *)
    output_values.
    match goal with [TT : p -PA- _ -PA> p' |- _] =>
      destruct (bc_outProc_out _ _ _ _ TT BS) as [R W2] end.
    destruct (bcWait_bisim_inj _ _ _ _ (bisim_trans _ _ _ (bisim_symm _ _ W2) W)) as [EM ET].
    subst m0. right. exists l0. split; [exact R | split; [symmetry; exact ET | reflexivity]].
Qed.

(** bcReady's only step is its broadcast of its mode and position on outProc.*)
Lemma bcReady_step_outProc (m : Mode) (l : Position) p p' b :
  bcReadyState m l p -> p -PA- b -PA> p' -> b = chanOutProc ;! [baseMode m, basePosition l].
Proof.
  intros R T. red in R. destruct (bisim_disc_match _ _ _ _ R T) as [q S].
  unfold bcReady in S. invert_disc_prefixes. output_values. reflexivity.
Qed.

(** No process is both bcReady and bcWait.*)
Local Lemma bcReady_not_bcWait (m m' : Mode) (l : Position) (x : Time) p :
  bcReadyState m l p -> bcWaitState m' x p -> False.
Proof.
  intros R W. red in R, W. pose proof (bisim_trans _ _ _ (bisim_symm _ _ R) W) as BT.
  unfold bcReady, bcWait in BT. refute_by_chan BT.
Qed.

Lemma bcWait_bktrk_net (n n' : Network) (m : Mode) (x : Time)
  (i : nat) (a : ActDiscNet) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
  bcWaitStateNet m x i n' ->
  bcWaitStateNet m x i n \/ x = zeroTime \/
  (exists l, bcReadyStateNet m l i n /\ x = period m /\
  sent [baseMode m, basePosition l] zeroTime i n' (reachNetDisc n n' a p w)).
(**Proof: Lift back tracking result.*)
Proof.
  intro BW. net_state_destr BW p1' p2' p3' l' h' k' E'.
  destruct (link_net_ent_disc_bkwd _ _ _ _ _ w E') as [e [E [EQ | [b S]]]].
  - subst e. left. net_state_intro E. exact BW.
  - destruct e as [q l h k].
    lets PS : reachableProtNet_triple p E. inversion PS as [p1 p2 p3 BS OS LS]; subst q.
    lets T : triple_disc_ent S. destruct T as [[EQ1 | [b1 B1]] _].
    + subst p1'. left. net_state_intro E. exact BW.
    + destruct (bcWait_prev _ _ _ _ _ B1 BS BW) as [Z | [l0 [R [X Eb]]]];
        [right; left; exact Z | right; right].
      exists l0. split; [net_state_intro E; exact R | split; [exact X | ]].
      (* the broadcaster took the step alone with the rest of the entity *)
      lets CU : reachableProt_correctChannelUsage
        (reachable_ent_prot _ _ _ _ (reachable_net_ent _ _ _ p E)).
      change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in CU, S.
      change (p1' $||$ p2' $||$ p3') with (parAll p1' [p2', p3']) in S.
      assert (ACT : forall c, p1 -PA- c -PA> p1' -> entChanAct c).
      { intros c TC. rewrite (bcReady_step_outProc _ _ _ _ _ R TC). right. reflexivity. }
      destruct (ent_disc_comp_chan _ _ _ _ _ _ _ _ _ _ _ _ _ 0 p1 p1' CU S eq_refl eq_refl
        eq_refl ACT) as [EQ | St].
      { subst p1'. exfalso. eapply bcReady_not_bcWait; eassumption. }
      positions_inv.
      assert (NE : p1 $||$ p2' $||$ p3' <> p1' $||$ p2' $||$ p3').
      { intro EQ. injection EQ as EQ. subst p1'. eapply bcReady_not_bcWait; eassumption. }
      lets TAU : procNeq_tau_net E E' w NE. subst a.
      inversion H2; subst;
        try solve [exfalso; eapply bcReady_not_bcWait; eassumption];
        try match goal with [TC : p1 -PA- ?c -PA> p1' |- _] =>
          let E2 := fresh in pose proof (bcReady_step_outProc _ _ _ _ _ R TC) as E2;
          try discriminate E2 end.
      match goal with [EV : chanOutProc ;! ?v = chanOutProc ;! _,
                       HI : h -i- chanOutProc {? ?v -i> h' |- _] =>
        injection EV as EV; subst v;
        eapply sentBase; [exact E | exact E' | apply stepDpParL; exact B1 | exact HI] end.
Qed.

Lemma msgAbortPathNet_urgent i n n' d :
  reachableProtNet n -> msgAbortPathNet i n -> n -ND- d -ND> n' -> False.
  intros. inversion H. link_netentdelfwd_tac e' LD.
  assert (reachableProtEnt e) as RE. eapply reachable_net_ent; eassumption.
  eapply msgAbortPathEnt_urgent; eassumption. Qed.
(**Proof: Synchronisation is always possible for the msgAbortPath states between the
listener component and either the position, the mode state or the overlap component.
Hence a delay would violate the noSynch property, and so cannot exist.*)

(*LOCAL TIDY*)

(** The notifBadPathNet relation can be broken down into the following cases.*)
Lemma notifBadPathNet_cases m i n :
  notifBadPathNet i n -> currModeNet m i n ->
  rangeBadStateNet m i n \/
  badOvlpStateNet i n.
  (*Proof: Similar to nexSinceStateNet_cases.*)
  intros. rename H0 into CMN. inversion H.
  inversion H0.
  apply currMode_ent_ex in CMN. ex_flat. and_flat.
  subst. entnetuniq2 EN n. subst. 
  left. eexists;[ | apply H1]. simpl.
  econstructor. assumption.
  subst. right. econstructor;[ | apply H1]. subst.
  constructor. assumption. Qed.

Lemma rangeBad_notifBad_net m i n :
  rangeBadStateNet m i n -> currModeNet m i n -> notifBadPathNet i n.
Proof.
  intros R C. destruct R as [e E1 E2].
  lets CM : liftEntNet_ent C E2.
  destruct E1 as [p l h k P]. simpl in CM.
  econstructor; [ | exact E2]. eapply nbpRng; [exact P | exact CM].
Qed.

Lemma badOvlp_notifBad_net i n :
  badOvlpStateNet i n -> notifBadPathNet i n.
Proof.
  intro H. destruct H as [e H1 H2]. destruct H1 as [p l h k H3].
  econstructor; [ | apply H2]. apply nbpBad. exact H3.
Qed.

Lemma ovReady_nextSince_state m t l i n :
  ovReadyStateNet m t l i n -> nextSinceStateNet i n.
Proof.
  intro H. destruct H as [e H1 H2]. destruct H1 as [p l' h k H3].
  inversion H3; subst.
  econstructor; [ | apply H2]. constructor. constructor.
  eapply nexsOvrSt. eassumption.
Qed.

End NARMisc.

(*-LOCAL TIDY*)
