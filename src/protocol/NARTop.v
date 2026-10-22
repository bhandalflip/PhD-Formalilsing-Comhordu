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
(*
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.EntityLanguage.*)
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtAuxResults.
(*Require Import ComhCoq.EntAux.*)
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults.

(*** Net Aux Results Imports ***)
Require Import ComhCoq.protocol.NARInsuff.
Require Import ComhCoq.protocol.NARMisc.
Require Import ComhCoq.protocol.NARMsgPosition.
Require Import ComhCoq.protocol.NARNonFS_currSince.
Require Import ComhCoq.protocol.NAROvlpTime.
Require Import ComhCoq.protocol.ProtocolBridge.

Section NARTop.
Context {Model : ComhModel}.

(* Let's say we can show that a network is currSince m t i n, then we can show
that the time parameter to this relation is always greater than mL + max AN trans,
which is the lower bound for the pre-sent interval.*)
Theorem currSince_lower_bound (n : Network) (t : Time) (m : Mode)
  (i : nat) (p : reachableProtNet n) : currSince m t i n p ->
  msgLatency + Rmax adaptNotif transMax < t.  
  (**Proof: Induction on currSince.*)
  intros. induction H.
  (*It's the base case that requires the most attention here. Well, we notice that
  the base case of currSince involves a proof of nextSince for the previous state.
  It also enforces the entity in the previous state to be in the state switchCurrState m.
  We prove elsewhere (NAROvlpTime::nextSince_switchCurr_lower) that nextSince, in this previous state,
  implies the lower bound. since the t is the same in the base case from premise to
  conclusion (passed on like a relay bat), this lower bound carries on to the t in
  currSince, and that's the base case done.*)
  apply (nextSince_switchCurr_lower n m i t p H H0).
  (*The inductive cases are the easy ones for once- because
  the parameter t to currSince is non-decreasing over these.*)
  assumption. apply Rplus_lt_weaken_rr. apply Rlt_le. delPos.
  assumption. Qed.

Lemma maxAnTrans_positive : 0 <= Rmax adaptNotif transMax.
  eapply Rle_trans;[ |apply Rmax_l]. timeNonneg. Qed.

(* If an entity has been awaiting a transition to a mode m for the past t time units,
and this t is bounded from below by mL + AN, then the entity in question has delivered
a message of <m, l0> to a sufficient radius r and l0, the position broadcast, differs
from the current position by at most Smax*t.*)
Theorem nextSince_fst_deliv_suff (n : Network) (t : Time) (m : Mode)
  (i : nat) (l : Position) (p : reachableProtNet n) : 
  nextSince m t i n p -> inPosNet l i n ->
  forall q : msgLatency + Rmax adaptNotif transMax < t,
  let s := (Rplus_lt_weaken_lr msgLatency (Rmax adaptNotif transMax)
  t q maxAnTrans_positive) in
  let s' := Rlt_le msgLatency t s in
  exists l0 l1 r,
  delivered ([-[baseMode m, basePosition l0], l1, r-]) (minusTime t msgLatency s') i n p /\ 
  sufficient m r /\ dist2d l l0 <= speedMax*t. 
  intros U0 U1 q. simpl.
  (*Well since mL + AN < t, then mL < t.*)
  assert (msgLatency < t) as MT. eapply Rplus_lt_weaken_lr. apply q.
  (*So by (NARMsgPosition::fst_delivered) we have that
  delivered <m, l0> r (t - mL) i n p /\ |l - l0| <= Smax*t.*)
  apply maxAnTrans_positive. lets FX : fst_delivered U0 U1 MT. decompEx3 FX l0 l1 r FD.
  decompAnd2 FD DE DI.
  (*This will do for our existential.*)
  exists l0 l1 r. splits;[my_applys_eq DE | | apply DI]. timering.
  (*So all that remains to be proven is the sufficiency of the radius r for the mode m.
  Now, again taking our inequality mL + AN < t we can easily obtain AN < t - mL.*)
  assert (adaptNotif < t - msgLatency) as AT. apply Rplus_lt_swap_ll in q.
  eapply Rle_lt_trans;[ |apply q]. apply Rmax_l.
  (*Also due to positive mL we have t - mL < t.*)
  assert (t - msgLatency < t). apply Rplus_lt_swap_rr. Rplus_lt_tac.
  apply msgLatency_positive.
  (*Hence by (deliv_next_suff) we get sufficient m r, and we're done.*)
  eapply deliv_next_suff. apply U0. apply DE. simpl. assumption. apply H.
  Qed.

(*TIDY*)

(** The wait time between two modes is positive.*)
Local Lemma waitTime_pos (m1 m2 : Mode) (pr : m1 -mtr-> m2) :
  0 < nonneg (time (waitTime m1 m2 pr)).
Proof.
  unfold waitTime. rewrite timeMax_RMax. eapply Rlt_le_trans; [ | apply Rmax_r].
  assert (DW : forall d : Delay, nonneg (time (delToTime d)) = pos (delay d))
    by (intros [[r rp]]; reflexivity).
  simpl. rewrite DW. pose proof msgLatency_positive. pose proof (cond_pos (delay waitSurplus)).
  pose proof (cond_nonneg (time (timeMax adaptNotif transMax))). simpl in *. lra.
Qed.

(** Truncated subtraction of r is injective on the numbers above r.*)
Local Lemma subNonnegTot_inj_pos (r1 r2 r : nonnegreal) :
  nonneg r < nonneg r1 -> r1 -nn- r = r2 -nn- r -> nonneg r1 = nonneg r2.
Proof.
  intros L E. apply (f_equal nonneg) in E. revert E. unfold subNonnegTot.
  destruct (Rle_dec r r1) as [L1 | L1]; destruct (Rle_dec r r2) as [L2 | L2]; simpl; lra.
Qed.

Lemma init_ovWait_track_net m m' t' i x y n n' a :
  initStateNet m i n -> ovWaitStateNet m' t' x y i n' ->
  n -NA- a -NA> n' -> m = m' /\ x = t' /\ y = zeroTime.
Proof.
  intros I OW S.
  destruct (init_ovWait_timers_net _ _ _ _ _ _ _ _ _ I OW S) as [EM [EY [[m0 [pr XV]] FV]]].
  subst m'. split; [reflexivity | split; [ | exact EY]].
  (* the first parameter is the wait time and a period, more than a period *)
  pose proof (waitTime_pos _ _ pr) as WP.
  apply timeEqR. apply (subNonnegTot_inj_pos _ _ (time (period m))); [ | symmetry; exact FV].
  rewrite XV. lra.
Qed.
(*Might prove a stronger version of this with the value of t' =
tx(m, m') + period m', where m is the current mode.*)

(*-TIDY*)

(** No entity has its overlap component in both ovReady and ovWait.*)
Local Lemma ovReady_ovWait_ent_not m t l0 m' t' x' y' q l h k l' h' k' :
  ovReadyStateEnt m t l0 ([|q, l, h, k|]) -> ovWaitStateEnt m' t' x' y' ([|q, l', h', k'|]) ->
  False.
Proof.
  intros OR OW. inversion OR as [q1 l1 h1 k1 ORq]; subst. inversion OW as [q2 l2 h2 k2 OWq]; subst.
  inversion ORq as [p1 p2 p3 OR2]; subst. inversion OWq as [p1' p2' p3' OW2 EQ]; subst.
  eapply ovReady_ovWait_bisim_not. eapply bisim_trans; [apply bisim_symm; exact OW2 | exact OR2].
Qed.

(* If we are in the wait state of the overlap component, and the y clock value is non-zero,
then a message containing the mode in question and some position was sent exactly
(period m - y) time units ago.  *)
Theorem ovWait_sent (n : Network) (m : Mode) (t x y : Time) (i : nat) (p : reachableProtNet n) : 
  ovWaitStateNet m t x y i n -> 0 < y ->
  exists l q,
  sent [baseMode m, basePosition l] (minusTime (period m) y q) i n p.  
  (*Induction on p.*)
Proof.
  intros OW YP. revert t x y OW YP.
  induction p as [n I | n n' a p IH w | n n' d p IH w]; intros t x y OW YP.
  - (* initially the overlap component is dormant, which no ovWait is *)
    exfalso. destruct OW as [e OWe E]. lets IE : initialNet_ent I E. inversion IE; subst.
    inversion OWe as [q lq hq kq OWq]; subst. unfold procProtocol in OWq.
    inversion OWq as [q1 q2 q3 OW2]; subst.
    destruct (dormant_mNext_in dormant m (bisim_refl _)) as [r S].
    destruct (bisim_disc_match _ _ _ _ OW2 S) as [r2 R2]. unfold ovWait in R2.
    invert_disc_prefixes.
  - (* a discrete step: back to ovWait, ovReady or init *)
    destruct (ovWait_prev_net _ _ _ _ _ _ _ _ p OW w) as [OWN | [[t0 [l0 [OR [_ EY]]]] | IS]].
    + destruct (IH _ _ _ OWN YP) as [l [q S]]. exists l q. apply sentDisc. exact S.
    + (* the broadcast of ovReady, which sent the message just now *)
      subst y. destruct OR as [e ORe E]. destruct OW as [e' OWe E'].
      destruct e as [q l h k]. destruct e' as [q' l' h' k'].
      destruct (link_net_ent_disc _ _ _ _ _ _ w E E') as [EQ | [a' S]].
      * exfalso. injection EQ as EQ1 EQ2 EQ3 EQ4. subst.
        eapply ovReady_ovWait_ent_not; [exact ORe | exact OWe].
      * assert (RE : reachableProtEnt ([|q, l, h, k|])) by (eapply reachableNet_ent; eassumption).
        lets BC : ovReady_ovWait_bcast_ent RE ORe OWe S.
        destruct BC as [TQ [TH [EK [_ EL]]]].
        lets PP : stepEnt_disc_pres_pos S. simpl in PP. subst l' k'.
        assert (NQ : q <> q').
        { intro EQ. subst q'. eapply ovReady_ovWait_ent_not; [exact ORe | exact OWe]. }
        lets TAU : procNeq_tau_net E E' w NQ. subst a.
        exists l0 (Rle_refl (period m)).
        replace (minusTime (period m) (period m) (Rle_refl (period m))) with zeroTime
          by (apply timeEqR; simpl; ring).
        eapply sentBase; eassumption.
    + (* init sets the position timer to zero *)
      destruct (init_ovWait_track_net _ _ _ _ _ _ _ _ _ IS OW w) as [_ [_ EY]].
      subst y. simpl in YP. lra.
  - (* a delay: the position timer was longer by the delay *)
    pose proof (proj1 (proj2 (reachableProtNet_del_prev _ _ _ _ _ p w OW))) as OS.
    destruct (ovWait_del_bkwd_net _ _ _ _ _ _ _ _ OS w OW) as [x1 OW1].
    assert (YP1 : 0 < nonneg (time (delToTime (y +dt+ d))))
      by (simpl; pose proof (cond_pos (delay d)); lra).
    destruct (IH _ _ _ OW1 YP1) as [l [q S]].
    assert (Q : nonneg (time y) <= nonneg (time (period m)))
      by (simpl in q; pose proof (cond_pos (delay d)); lra).
    exists l Q.
    replace (minusTime (period m) y Q)
      with (delToTime (minusTime (period m) (delToTime (y +dt+ d)) q +dt+ d))
      by (apply timeEqR; simpl; ring).
    apply sentDel. exact S.
Qed.

(* Let's say an entity has been awaiting transition to the mode m since t time units ago.
Then for any t' < t, we can assert that a message was sent containing the mode in
question m and some position l0 within the window t' and t' + period m. We also know
that the message was sent at most t units ago.*)
Theorem nextSince_periodic_sent (n : Network) (m : Mode) (t t' : Time)
  (i : nat) (p : reachableProtNet n) :
  nextSince m t i n p -> t' < t ->
  exists t'' l,
  t' < (time t'') <= t' + period m /\ t'' <= t /\
  sent [baseMode m, basePosition l] t'' i n p. 
  (*The proof should resemble that of currSince_periodic_sent. Here's an illustrative
  intuitive diagram for it:
  nextSince-------------t------------
    [  period m )--------t'----------
        sent------------t''----------*)
  intros. gen t'.
  (*Induction on nextSince.*)
  induction H; intros.
  (*The base case with t = 0 fails becasue then we'd have t' < 0, which contradicts
  the non negativity of time.*)
  contradict H2. apply Rle_not_lt. simpl. timeNonneg.
  (*The discrete inductive case follows by simple application of the inductive hypothesis
  and then the discrete sent constructor.*)
  lets IH : IHnextSince H1. clear IHnextSince. decompEx2 IH t'' l W.
  andflat Y. exists t'' l. splits; try assumption. split; assumption.
  constructor. assumption.
  (*Leaving us with just the timed inductive case to solve. Here we apply
  (Misc::nextSince_rel_state) to get the possible states for nextSince.*)
  lets NR : nextSince_rel_state H.
  (*We show by (...EA::urgency...) that the only such state capable of delay is ovWait.*)
  lets ND : nextSince_del_ovWait_pos p w NR. decompEx4 ND m0 t0 x y OS. assert (m0 = m) as ME.
  eapply nextSince_ovWait_modes_eq. apply OS. apply H.
  (*We then proceed analogously to currSince_periodic_sent, case analysing on d <= t' or
  t' < d etc. only we use (ovWait_sent) in the place of (bcWait_sent).*)
  lets RO : Rle_or_lt d t'. elim_intro RO DT TD.
  (*In the former case, we can show then that t' = t'' + d for some t''.*)
  assert (exists t'', nonneg t' = (time t'') + d) as TX. apply RlePlusExistsR in DT.
  invertClearAs2 DT dt TE. decompAnd2 TE TP TL. rewrite Rplus_comm in TP.
  exists (mkTime (mknonnegreal dt TL)). apply TP. invertClearAs2 TX t'' TE.
  (*Now, we also know t' < t + d, so t'' < t*)
  assert (t'' < t) as TL. rewrite TE in H0. simpl in H0. Rplus_lt_tac.
  (*So we can apply the I.H. for t'' and the previous state*)
  apply IHnextSince in TL. clear IHnextSince. decompEx2 TL u l TA.
  andflat T.
  (*So our existential becomes u + d*)
  exists (u +dt+ d) l.
  (*Now we need to show inequality the sub-cases of our goal by a bit of algebraic manipulation*)
  splits. rewrite TE. simpl.
  split. Rplus_lt_tac. Rplus3_swap_2_3 t'' d (period m). Rplus_le_tac. simpl. Rplus_le_tac.
  (*Then apply the sent delay constructor and we're done.*)
  constructor. assumption.
  (*Now all that remains is the delay case where t' < d. Well we already know that the previous state
  was ovWait m0 t0 (x + d) (y + d). So by (ovWait_sent) we get
  sent <m, l> (period m - (x + d)) for the previous case*)
  assert (zeroTime < (delToTime (y +dt+ d))) as YD. simpl. replace 0 with (0 + 0).
  apply Rplus_le_lt_compat. timeNonneg. delPos. ring.
  lets SX : ovWait_sent p OS YD. decompEx2 SX l q SE.
  (*So for the current case our existential is period m - y*)
  assert (y <= period m0) as YL. simpl in q. eapply Rplus_le_weaken_lr.
  apply q. apply Rlt_le. delPos.
  exists (minusTime (period m0) y YL) l. simpl in q, YD. simpl. splits.
  (*And now we clean up the inequalitites.*)
  split. simpl. eapply Rlt_le_trans. apply TD. Rplus_le_tac.
  simpl. rewrite Rplus_comm. rewrite ME. 
  Rminus_plus_zero (period m) y. Rplus_le_tac. apply Rplus_le_swap_rr.
  replace 0 with (0 + 0). apply Rplus_le_compat; timeNonneg. ring.
  rewrite <- ME in H. lets ON : ovWait_nextSince_time OS H. simpl in ON.
  apply Rminus_le_swap_lr. my_applys_eq ON. ring. generalize dependent YL.
  rewrite <- ME. intro YL. lets SD : sentDel p w SE. my_applys_eq SD.
  timering. Qed.

(** switchBc's only step wakes the broadcaster in its mode.*)
Local Lemma switchBc_step_wake (m : Mode) p p' c :
  switchBcState m p -> p -PA- c -PA> p' -> c = chanWake ;! [baseMode m].
Proof.
  intros R T. red in R. destruct (bisim_disc_match _ _ _ _ R T) as [q S].
  unfold switchBc in S. invert_disc_prefixes. output_values. reflexivity.
Qed.

(** The listener never inputs on wake.*)
Local Lemma listener_wake_in_not p p' v :
  listenerState p -> p -PA- chanWake ;? v -PA> p' -> False.
Proof. intros S T. destruct (listenerState_shape _ S); prot_outProc_in_not_contra. Qed.

(** A step in which the overlap component leaves switchBc m for switchCurr wakes the
broadcaster in mode m.*)
Local Lemma switchBc_switchCurr_ent_wake m p1 p2 p3 p1' p2' p3' l l' h h' k k' b :
  broadcastState p1 -> overlapState p2 -> listenerState p3 ->
  switchBcState m p2 -> switchCurrState p2' ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- b ->> [|p1' $||$ p2' $||$ p3', l', h', k'|] ->
  p1 -PA- chanWake ;? [baseMode m] -PA> p1'.
Proof.
  intros BS OS LS SB SC S.
  assert (NE : p2 <> p2').
  { intro EQ; subst p2'. red in SB, SC.
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ SB) SC) as BT. ovWait_bisim_contra BT. }
  inversion S; subst;
    try (exfalso; apply NE; reflexivity);
    try match goal with [T : _ $||$ _ $||$ _ -PA- ?c -PA> _ $||$ _ $||$ _ |- _] =>
      first [ (lets TT : link_reach_triple_tau T (protState _ _ _ BS OS LS);
               destruct TT as [c0 [v0 TT]];
               decompose [or and] TT; clear TT; subst;
               try (exfalso; apply NE; reflexivity);
               match goal with
               | [T2 : p2 -PA- c0 ;? v0 -PA> p2' |- _] =>
                 exfalso; lets E2 : switchBc_step_wake SB T2; discriminate E2
               | [T2 : p2 -PA- c0 ;! v0 -PA> p2' |- _] =>
                 lets E2 : switchBc_step_wake SB T2; injection E2 as E2a E2b; subst c0 v0;
                 first [ assumption
                       | exfalso; eapply listener_wake_in_not; eassumption ]
               end)
            | (triple_disc_nonTau T;
               first [ exfalso; apply NE; reflexivity
                     | match goal with [T2 : p2 -PA- _ -PA> _ |- _] =>
                         exfalso; lets E2 : switchBc_step_wake SB T2; discriminate E2 end ]) ]
    end.
Qed.

(** Woken in mode m, the broadcaster waits in mode m with its timer zero.*)
Local Lemma broadcast_wake_in (m : Mode) p p' : broadcastState p ->
  p -PA- chanWake ;? [baseMode m] -PA> p' -> bcWaitState m zeroTime p'.
Proof.
  intros BS T. destruct (broadcastState_shape _ BS) as [B | m0 e B | m0 l B];
    destruct (bisim_step_disc _ _ _ _ B T) as [q [TQ BQ]]; prot_outProc_in_not_body;
    invert_disc_prefixes; explicit_typed_input.
  all: red; clean_proc_hyp BQ; (eapply bisim_trans; [exact BQ | ]); unfold_app_bisim;
    apply bisim_refl.
Qed.

(** The broadcaster waits or is ready to broadcast in mode m.*)
Local Definition bcModeState (m : Mode) (p : ProcTerm) : Prop :=
  (exists x, bcWaitState m x p) \/ (exists l, bcReadyState m l p).

(** A wait reads its position into bcReady, or takes trans or wake.*)
Local Lemma bcWait_step_cases (m : Mode) (x : Time) p p' c :
  bcWaitState m x p -> p -PA- c -PA> p' ->
  (exists (l : Position), c = chanPos ;? [basePosition l] /\ bcReadyState m l p') \/
  (exists v, c = chanTrans ;? v) \/ (exists v, c = chanWake ;? v).
Proof.
  intros W T. red in W. destruct (bisim_step_disc _ _ _ _ W T) as [q [TQ BQ]].
  unfold bcWait in TQ. invert_disc_prefixes; try (unfold liftVarList in *); explicit_typed_input.
  - right. left. eexists. reflexivity.
  - left. eexists. split; [reflexivity | ]. red. clean_proc_hyp BQ.
    eapply bisim_trans; [exact BQ | ]. unfold_app_bisim. apply bisim_refl.
  - right. right. eexists. reflexivity.
Qed.

(** A broadcaster in mode m stays in mode m through its own steps, but for an input on trans or
wake.*)
Local Lemma bcMode_comp_step (m : Mode) p p' c :
  bcModeState m p -> broadcastState p -> p -PA- c -PA> p' ->
  bcModeState m p' \/ (exists v, c = chanTrans ;? v) \/ (exists v, c = chanWake ;? v).
Proof.
  intros [[x W] | [l R]] BS T.
  - destruct (bcWait_step_cases _ _ _ _ _ W T) as [[l [_ R]] | [V | V]].
    + left. right. exists l. exact R.
    + right. left. exact V.
    + right. right. exact V.
  - left. left. exists (period m). rewrite (bcReady_step_outProc _ _ _ _ _ R T) in T.
    exact (proj2 (bc_outProc_out _ _ _ _ T BS)).
Qed.

(** Only tfsBc outputs on trans, and it goes to tfsListen.*)
Local Lemma overlap_trans_out p p' v : overlapState p -> p -PA- chanTrans ;! v -PA> p' ->
  tfsBcState p /\ tfsListenState p'.
Proof.
  intros O T. destruct (overlapState_shape _ O)
    as [B | m B | m e2 e3 e4 B | m e2 l B | m B | B | B | B | B | m B | B | B | B];
    try solve [exfalso; destruct (bisim_disc_match _ _ _ _ B T) as [q TQ];
      prot_outProc_in_not_body; invert_disc_prefixes].
  split; [exact B | ]. destruct (bisim_step_disc _ _ _ _ B T) as [q [TQ BQ]].
  unfold tfsBc in TQ. invert_disc_prefixes. red. clean_proc_hyp BQ.
  eapply bisim_trans; [exact BQ | ]. unfold_app_bisim. apply bisim_refl.
Qed.

(** Only switchBc outputs on wake: it wakes the broadcaster in its mode and goes to switchCurr.*)
Local Lemma overlap_wake_out p p' v : overlapState p -> p -PA- chanWake ;! v -PA> p' ->
  exists (m : Mode), v = [baseMode m] /\ switchBcState m p /\ switchCurrState p'.
Proof.
  intros O T. destruct (overlapState_shape _ O)
    as [B | m B | m e2 e3 e4 B | m e2 l B | m B | B | B | B | B | m B | B | B | B];
    try solve [exfalso; destruct (bisim_disc_match _ _ _ _ B T) as [q TQ];
      prot_outProc_in_not_body; invert_disc_prefixes].
  exists m. destruct (bisim_step_disc _ _ _ _ B T) as [q [TQ BQ]].
  unfold switchBc in TQ. invert_disc_prefixes. output_values.
  split; [reflexivity | split; [exact B | ]]. red. clean_proc_hyp BQ.
  eapply bisim_trans; [exact BQ | ]. unfold_app_bisim. apply bisim_refl.
Qed.

(** The listener never outputs on trans or wake.*)
Local Lemma listener_trans_wake_out_not p p' c v : listenerState p ->
  (c = chanTrans \/ c = chanWake) -> p -PA- c ;! v -PA> p' -> False.
Proof.
  intros S [E | E] T; subst c; destruct (listenerState_shape _ S); prot_outProc_in_not_contra.
Qed.

(** An entity step leaves a broadcaster in mode m in mode m, unless it is tfsBc's trans or
switchBc's wake-up.*)
Local Lemma bcMode_step_ent m p1 p2 p3 p1' p2' p3' l l' h h' k k' b :
  broadcastState p1 -> overlapState p2 -> listenerState p3 -> bcModeState m p1 ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- b ->> [|p1' $||$ p2' $||$ p3', l', h', k'|] ->
  bcModeState m p1' \/ (tfsBcState p2 /\ tfsListenState p2') \/
  (exists m', switchBcState m' p2 /\ switchCurrState p2').
Proof.
  intros BS OS LS BM S.
  inversion S; subst; try (left; exact BM).
  all: match goal with [T : _ $||$ _ $||$ _ -PA- ?c -PA> _ $||$ _ $||$ _ |- _] =>
    first [
      (* a tau: two components synchronise *)
      (destruct (link_reach_triple_tau _ _ _ _ _ _ T (protState _ _ _ BS OS LS)) as [c0 [v0 TT]];
       destruct TT as [[T1 [T2 E3]] | [[T1 [T2 E3]] | [[T1 [T3 E2]] | [[T1 [T3 E2]]
         | [[T2 [T3 E1]] | [T2 [T3 E1]]]]]]];
       [ destruct (bcMode_comp_step _ _ _ _ BM BS T1) as [BM' | [[vt E] | [vt E]]];
           [left; exact BM' | discriminate E | discriminate E]
       | destruct (bcMode_comp_step _ _ _ _ BM BS T1) as [BM' | [[vt E] | [vt E]]];
           [ left; exact BM'
           | injection E as EC EV; subst; right; left; exact (overlap_trans_out _ _ _ OS T2)
           | injection E as EC EV; subst; right; right;
             destruct (overlap_wake_out _ _ _ OS T2) as [m' [_ [SB SC]]];
             exists m'; split; assumption ]
       | destruct (bcMode_comp_step _ _ _ _ BM BS T1) as [BM' | [[vt E] | [vt E]]];
           [left; exact BM' | discriminate E | discriminate E]
       | destruct (bcMode_comp_step _ _ _ _ BM BS T1) as [BM' | [[vt E] | [vt E]]];
           [ left; exact BM'
           | injection E as EC EV; subst; exfalso;
             exact (listener_trans_wake_out_not _ _ _ _ LS (or_introl eq_refl) T3)
           | injection E as EC EV; subst; exfalso;
             exact (listener_trans_wake_out_not _ _ _ _ LS (or_intror eq_refl) T3) ]
       | subst; left; exact BM
       | subst; left; exact BM ])
    | (* not a tau: one component steps with the entity *)
      (triple_disc_nonTau T;
       first [ left; exact BM
             | match goal with [T1 : ?q -PA- _ -PA> _, BM0 : bcModeState _ ?q,
                                BS0 : broadcastState ?q |- _] =>
                 destruct (bcMode_comp_step _ _ _ _ BM0 BS0 T1) as [BM' | [[vt E] | [vt E]]];
                 [left; exact BM' | discriminate E | discriminate E] end ]) ]
  end.
Qed.

(** switchCurr's one step is its write on mCurr, into switchListen.*)
Local Lemma switchCurr_step_listen p p' b :
  switchCurrState p -> p -PA- b -PA> p' -> switchListenState p'.
Proof.
  intros SC T. red in SC. destruct (bisim_step_disc _ _ _ _ SC T) as [q [TQ BQ]].
  unfold switchCurr in TQ. invert_disc_prefixes. red. clean_proc_hyp BQ.
  eapply bisim_trans; [exact BQ | ]. unfold_app_bisim. apply bisim_refl.
Qed.

(** The broadcaster is in mode m, as a network state predicate.*)
Local Definition bcModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
  liftEntNet (liftProcEnt (liftBroadcast (bcModeState m))) i n.

Local Lemma bcModeNet_cases m i n : bcModeNet m i n ->
  (exists x, bcWaitStateNet m x i n) \/ (exists l, bcReadyStateNet m l i n).
Proof.
  intro BM. net_state_destr BM p1 p2 p3 l h k E.
  destruct BM as [[x W] | [l0 R]]; [left; exists x | right; exists l0]; net_state_intro E;
    assumption.
Qed.

(** A network step leaves a broadcaster in mode m in mode m, unless it is tfsBc's trans or
switchBc's wake-up.*)
Local Lemma bcMode_step_net m n n' a i :
  reachableProtNet n -> n -NA- a -NA> n' -> bcModeNet m i n ->
  bcModeNet m i n' \/ (tfsBcStateNet i n /\ tfsListenStateNet i n') \/
  (exists m', switchBcStateNet m' i n /\ switchCurrStateNet i n').
Proof.
  intros R S BM. net_state_destr BM p1 p2 p3 l h k E.
  lets PS : reachableProtNet_triple R E. inversion PS as [q1 q2 q3 BS OS LS]; subst.
  destruct (link_net_ent_disc_fwd _ _ _ _ _ S E) as [e' [E' [EQ | [b ST]]]].
  - subst e'. left. net_state_intro E'. exact BM.
  - destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ ST) as [p1' [p2' [p3' [l' [h' [k' [EE _]]]]]]].
    subst e'.
    destruct (bcMode_step_ent _ _ _ _ _ _ _ _ _ _ _ _ _ _ BS OS LS BM ST)
      as [BM' | [[TB TL] | [m' [SB SC]]]].
    + left. net_state_intro E'. exact BM'.
    + right. left. split; [net_state_intro E | net_state_intro E']; assumption.
    + right. right. exists m'. split; [net_state_intro E | net_state_intro E']; assumption.
Qed.

(** A network step from switchCurr stays in switchCurr or goes to switchListen.*)
Local Lemma switchCurr_step_net n n' a i :
  reachableProtNet n -> n -NA- a -NA> n' -> switchCurrStateNet i n ->
  switchCurrStateNet i n' \/ switchListenStateNet i n'.
Proof.
  intros R S SC. net_state_destr SC p1 p2 p3 l h k E.
  destruct (link_net_ent_disc_fwd _ _ _ _ _ S E) as [e' [E' [EQ | [b ST]]]].
  - subst e'. left. net_state_intro E'. exact SC.
  - destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ ST)
      as [p1' [p2' [p3' [l' [h' [k' [EE [_ [[EQ2 | [b2 B2]] _]]]]]]]]]; subst e'.
    + subst p2'. left. net_state_intro E'. exact SC.
    + right. net_state_intro E'. exact (switchCurr_step_listen _ _ _ SC B2).
Qed.

(** An entity whose broadcaster waits with timer x cannot let more than x pass: when the timer
runs out it reads its position, and no time passes while it can.*)
Local Lemma bcWait_del_timer_ge (m : Mode) (x : Time) p1 p2 p3 l h k (d : Delay) e' :
  bcWaitState m x p1 -> [|p1 $||$ p2 $||$ p3, l, h, k|] -ED- d ->> e' -> pos (delay d) <= x.
Proof.
  intros W DE. destruct (Rle_or_lt (pos (delay d)) x) as [LE | LT]; [exact LE | exfalso].
  destruct (bcWait_pos_read m x) as [[Z [q R]] | [dx [q [EX [TD [q' R]]]]]].
  - eapply ent_del_pos_in_not; [ | exact DE]. dae_broadcast.
    destruct (bisim_disc_match _ _ _ _ (bisim_symm _ _ W) R) as [r R']. exists r. exact R'.
  - inversion DE as [d0 p p'' l0 delta i0 i'' k0 k'' PD ID KD DISP NS]; subst.
    assert (POS : 0 < pos (delay d) - pos (delay dx)) by (simpl in *; lra).
    set (d2 := mkDelay (mkposreal _ POS)).
    assert (DS : d = dx +d+ d2) by (apply delayEqR; simpl; lra).
    clearbody d2.
    destruct (timeSplit _ _ _ _ _ PD DS) as [pm [PD1 _]].
    destruct (timeSplit_inter _ _ _ _ _ ID DS) as [hm [ID1 _]].
    destruct (timeSplit_mState _ _ _ _ _ KD DS) as [km [KD1 _]].
    destruct (NS (chanPos ;? [basePosition origin])) as [_ NS2].
    assert (LTd : dx < d) by (simpl in *; lra).
    specialize (NS2 pm hm km dx LTd PD1 ID1 KD1).
    triple_del_inv PD1.
    match type of NS2 with noSyncNow _ (parAll ?a [?b, ?c]) _ _ =>
      match goal with [D1 : p1 -PD- dx -PD> a |- _] =>
    destruct (bisim_step_del _ _ _ _ W D1) as [q1 [TQ1 BQ1]];
    assert (RD1 : exists r, q1 -PA- chanPos ;? [basePosition origin] -PA> r);
    [ destruct (bcWait_del_cases _ _ _ _ TQ1) as [[t [H [EV EQ]]] | [[t [EV [_ RD]]] | [EV _]]];
      [ subst q1; unfold liftTimeExp in EV; rewrite evalExpFunTime_time in EV;
        injection EV as EV; subst t;
        destruct (bcWait_pos_read m (minusTime x dx H)) as [[_ RD] | [d3 [q3 [EQ3 _]]]];
          [exact RD | exfalso; simpl in EQ3; pose proof (cond_pos (delay d3)); lra]
      | exact RD
      | unfold liftTimeExp in EV; rewrite evalExpFunTime_time in EV; discriminate EV ]
    | destruct RD1 as [r RD1];
      destruct (bisim_disc_match _ _ _ _ (bisim_symm _ _ BQ1) RD1) as [r' R1];
      assert (DA : discActEnabled (a $||$ b $||$ c) (chanPos ;? [basePosition origin]))
        by (dae_broadcast; exists r'; exact R1);
      exact (proj2 (proj2 (NS2 DA)) origin eq_refl) ] end end.
Qed.

(** A network delay leaves a broadcaster in mode m in mode m: bcReady cannot delay, and a wait
counts down.*)
Local Lemma bcMode_del_net m n n' d i :
  reachableProtNet n -> n -ND- d -ND> n' -> bcModeNet m i n -> bcModeNet m i n'.
Proof.
  intros R D BM. net_state_destr BM p1 p2 p3 l h k E.
  destruct (link_net_ent_del_fwd _ _ _ _ _ D E) as [e' [E' DE]].
  destruct e' as [q l' h' k'].
  lets PS : reachableProtNet_triple (reachNetDel _ _ _ R D) E'.
  inversion PS as [p1' p2' p3' BS' OS' LS']; subst q.
  destruct (triple_del_ent _ _ _ _ _ _ _ _ _ _ _ _ _ DE) as [D1 _].
  net_state_intro E'.
  destruct BM as [[x W] | [l0 RD]].
  - left. pose proof (bcWait_del_timer_ge _ _ _ _ _ _ _ _ _ _ W DE) as LE.
    destruct (bisim_step_del _ _ _ _ W D1) as [q [TQ BQ]].
    destruct (bcWait_del_cases _ _ _ _ TQ) as [[t [H [EV EQ]]] | [[t [EV [LT2 _]]] | [EV _]]].
    + subst q. unfold liftTimeExp in EV. rewrite evalExpFunTime_time in EV.
      injection EV as EV. subst t. exists (minusTime x d H). exact BQ.
    + exfalso. unfold liftTimeExp in EV. rewrite evalExpFunTime_time in EV.
      injection EV as EV. subst t. lra.
    + exfalso. unfold liftTimeExp in EV. rewrite evalExpFunTime_time in EV. discriminate EV.
  - exfalso. eapply (bcReady_urgent m l0); [ | exact DE]. constructor. constructor. exact RD.
Qed.

(** A delay keeps switchCurr.*)
Local Lemma switchCurr_del_net n n' d i :
  reachableProtNet n -> n -ND- d -ND> n' -> switchCurrStateNet i n -> switchCurrStateNet i n'.
Proof.
  intros R D SC. net_state_destr SC p1 p2 p3 l h k E.
  destruct (link_net_ent_del_fwd _ _ _ _ _ D E) as [e' [E' DE]].
  destruct e' as [q l' h' k'].
  lets PS : reachableProtNet_triple (reachNetDel _ _ _ R D) E'.
  inversion PS as [p1' p2' p3' BS' OS' LS']; subst q.
  destruct (triple_del_ent _ _ _ _ _ _ _ _ _ _ _ _ _ DE) as [_ [D2 _]].
  net_state_intro E'. red. eapply bisim_del_pres; [del_self_body | exact SC | exact D2].
Qed.

(** While entity i is nextSince m and in switchCurr, its broadcaster is in mode m, in which
switchBc m woke it.*)
Local Lemma nextSince_switchCurr_bcMode m t i n (p : reachableProtNet n) :
  nextSince m t i n p -> switchCurrStateNet i n -> bcModeNet m i n.
Proof.
  intro NS. induction NS as [a i n n' p w l t t' x y PE OR OW | a t i n n' p w NS IH NSS
    | d t i n n' p w NS IH]; intro SC.
  - exfalso. pose proof (overlap_states_bisim_net _ _ _ _ OW SC) as BT. ovWait_bisim_contra BT.
  - assert (STAY : switchCurrStateNet i n -> bcModeNet m i n').
    { intro SC0.
      destruct (bcMode_step_net _ _ _ _ _ p w (IH SC0)) as [BM | [[TB _] | [m' [SB _]]]].
      - exact BM.
      - exfalso. pose proof (overlap_states_bisim_net _ _ _ _ TB SC0) as BT.
        ovWait_bisim_contra BT.
      - exfalso. pose proof (overlap_states_bisim_net _ _ _ _ SB SC0) as BT.
        ovWait_bisim_contra BT. }
    pose proof SC as SC'. net_state_destr SC' p1' p2' p3' l' h' k' E'.
    destruct (link_net_ent_disc_bkwd _ _ _ _ _ w E') as [e [E [EQ | [b ST]]]].
    + subst e. apply STAY. net_state_intro E. exact SC'.
    + destruct e as [q l h k]. lets PS : reachableProtNet_triple p E.
      inversion PS as [p1 p2 p3 BS OS LS]; subst q.
      lets T : triple_disc_ent ST. destruct T as [_ [[EQ2 | [b2 B2]] _]].
      * subst p2'. apply STAY. net_state_intro E. exact SC'.
      * (* the wake-up by switchBc, for the mode m of nextSince *)
        destruct (switchCurr_prev _ _ _ B2 OS SC') as [m0 SB0].
        assert (SBn : switchBcStateNet m0 i n) by (net_state_intro E; exact SB0).
        rewrite <- (nextSince_switchBc_modeEq _ _ _ _ _ _ NS SBn) in SB0.
        net_state_intro E'. left. exists zeroTime.
        exact (broadcast_wake_in _ _ _ BS
          (switchBc_switchCurr_ent_wake _ _ _ _ _ _ _ _ _ _ _ _ _ _ BS OS LS SB0 SC' ST)).
  - destruct (reachableProtNet_del_prev _ _ _ _ _ p w SC) as [_ [OS _]].
    assert (SC0 : switchCurrStateNet i n)
      by (apply (overlap_del_bkwd_net switchCurr _ _ _ _ OS w SC); intros m0 e2 e3 e4 B;
          ovWait_bisim_contra B).
    exact (bcMode_del_net _ _ _ _ _ p w (IH SC0)).
Qed.

(** While an entity is currSince a mode that is not fail safe, and not in switchCurr, its
broadcaster is in that mode.*)
Local Lemma currSince_bcMode m t i n (p : reachableProtNet n) :
  currSince m t i n p -> ~ failSafe m -> ~ switchCurrStateNet i n -> bcModeNet m i n.
Proof.
  intros CS NF.
  induction CS as [a t i n n' p w NS SC SL | a t i n n' p w CS IH CM | d t i n n' p w CS IH];
    intro NSC.
  - destruct (bcMode_step_net _ _ _ _ _ p w (nextSince_switchCurr_bcMode _ _ _ _ _ NS SC))
      as [BM' | [[TB _] | [m' [SB _]]]].
    + exact BM'.
    + exfalso. pose proof (overlap_states_bisim_net _ _ _ _ TB SC) as BT. ovWait_bisim_contra BT.
    + exfalso. pose proof (overlap_states_bisim_net _ _ _ _ SB SC) as BT. ovWait_bisim_contra BT.
  - destruct (Classical_Prop.classic (switchCurrStateNet i n)) as [SC | NSC0].
    + (* the switch from switchCurr makes its next mode current, so m *)
      destruct (switchCurr_nextSince_ex n p i SC) as [m2 [t2 NS2]].
      destruct (switchCurr_step_net _ _ _ _ p w SC) as [SC' | SL]; [contradiction | ].
      pose proof (switch_states_mState _ _ _ _ _ p w SC SL (nextSince_next _ _ _ _ _ NS2)) as CM2.
      assert (EM : m2 = m).
      { rewrite currMode_ent_ex in CM, CM2. destruct CM as [e [E CE]], CM2 as [e2 [E2 CE2]].
        assert (e2 = e) by (eapply entInNetUnique; eassumption). subst e2. congruence. }
      subst m2.
      destruct (bcMode_step_net _ _ _ _ _ p w (nextSince_switchCurr_bcMode _ _ _ _ _ NS2 SC))
        as [BM' | [[TB _] | [m' [SB _]]]].
      * exact BM'.
      * exfalso. pose proof (overlap_states_bisim_net _ _ _ _ TB SC) as BT.
        ovWait_bisim_contra BT.
      * exfalso. pose proof (overlap_states_bisim_net _ _ _ _ SB SC) as BT.
        ovWait_bisim_contra BT.
    + destruct (bcMode_step_net _ _ _ _ _ p w (IH NSC0)) as [BM' | [[TB TL] | [m' [SB SC']]]].
      * exact BM'.
      * exfalso. apply NF. exact (tfsListen_failSafe_net m i n' (reachNetDisc _ _ _ p w) TL CM).
      * exfalso. exact (NSC SC').
  - assert (NSC0 : ~ switchCurrStateNet i n)
      by (intro SC; exact (NSC (switchCurr_del_net _ _ _ _ p w SC))).
    exact (bcMode_del_net _ _ _ _ _ p w (IH NSC0)).
Qed.

(*Relates the currSince relation to the state of the broadcast software
component. In particular, if we're currSince, then the broadcast component is either
waiting to broadcast or ready to broadcast.*)
Theorem currSince_bc_state (n : Network) (m : Mode) (t : Time)
  (i : nat) (p : reachableProtNet n) : currSince m t i n p -> ~ failSafe m ->
  ~ switchCurrStateNet i n ->
  (exists x, bcWaitStateNet m x i n) \/
  (exists l, bcReadyStateNet m l i n).
(**Proof: Induction on currSince. In the base case, we have that the overlap component has
gone from switchCurr to switchListen, in which case the broadcast component can be shown to
have stayed the same (...). But in a separate result (...EA::inter_component...) we can
show that switchCurrState m implies bcWaitState m, and since the broadcast component has
not changed across the transition, we have our left disjunct to satisfy our goal. Now,
for the inductive cases, we can apply the I.H. and then do a case analysis on the previous
state.
For the bcReady state, we can show (...fwd_track...) that it is either preserved or
transitions to bcWait by a discrete transition, giving us our goal. We can also show that
is urgent, allowing us to proceed with a contradiction in the delay inductive case.
For the bcWait state, it is easy to show (...delay_pres_state...) that the delay transition
preserves this state. For the discrete transition case, we assume that our goal does not
hold towards a contradiction. Well then the broadcast component must be in the sleeping
state. Then we can show (...tracking...) that the action linking the states must be a tau,
with the broadcast component contributing an input on trans. Now, it can be shown
(...activation...) that the only state willing to output on trans is tfsBc. But we can show
elsewhere (tfsBc_not_currSince) that tfsBc implies that we are not currSince, which
contradicts the hypothesis.*)
Proof. intros CS NF NSC. exact (bcModeNet_cases _ _ _ (currSince_bcMode _ _ _ _ _ CS NF NSC)). Qed.

(** If we're currSince & we can delay, then we're in the bcWait state.*)
Corollary currSince_del_bcWait (n n' : Network) (m : Mode) (t : Time)
  (i : nat) (d : Delay) (p : reachableProtNet n) :
  n -ND- d -ND> n' -> currSince m t i n p -> ~ failSafe m ->
  exists x, bcWaitStateNet m (delToTime (x +dt+ d)) i n.
(**Proof: Apply currSince_bc_state and then eliminate bcReady as it is urgent*)
Proof.
  intros D CS NF.
  assert (NSC : ~ switchCurrStateNet i n).
  { intro SC. destruct SC as [e SCe E]. destruct (link_net_ent_del_fwd _ _ _ _ _ D E) as [e' [_ DE]].
    exact (swithcCurr_urgent m e e' d (reachable_net_ent _ _ _ p E) SCe DE). }
  destruct (currSince_bc_state n m t i p CS NF NSC) as [[x W] | [l R]].
  - pose proof W as W'. net_state_destr W' p1 p2 p3 l h k E.
    destruct (link_net_ent_del_fwd _ _ _ _ _ D E) as [e' [_ DE]].
    pose proof (bcWait_del_timer_ge _ _ _ _ _ _ _ _ _ _ W' DE) as LE.
    exists (minusTime x d LE).
    assert (EQ : delToTime (minusTime x d LE +dt+ d) = x) by (apply timeEqR; simpl; ring).
    rewrite EQ. exact W.
  - exfalso. destruct R as [e Re E]. destruct (link_net_ent_del_fwd _ _ _ _ _ D E) as [e' [_ DE]].
    exact (bcReady_urgent m l e e' d Re DE).
Qed.

(** After a step into switchCurr, the overlap component was in switchCurr already, or the step
woke the broadcaster, whose timer is then zero.*)
Local Lemma switchCurr_prev_net_bcWait n n' i a m x :
  reachableProtNet n -> n -NA- a -NA> n' -> switchCurrStateNet i n' ->
  bcWaitStateNet m x i n' -> switchCurrStateNet i n \/ x = zeroTime.
Proof.
  intros R S SC BW. net_state_destr SC p1' p2' p3' l' h' k' E'.
  net_state_ent BW E'.
  destruct (link_net_ent_disc_bkwd _ _ _ _ _ S E') as [e [E [EQ | [b ST]]]].
  - subst e. left. net_state_intro E. exact SC.
  - destruct e as [q l h k]. lets PS : reachableProtNet_triple R E.
    inversion PS as [p1 p2 p3 BS OS LS]; subst q.
    lets T : triple_disc_ent ST. destruct T as [_ [[EQ2 | [b2 B2]] _]].
    + subst p2'. left. net_state_intro E. exact SC.
    + right. destruct (switchCurr_prev _ _ _ B2 OS SC) as [m0 SB].
      pose proof (broadcast_wake_in _ _ _ BS
        (switchBc_switchCurr_ent_wake _ _ _ _ _ _ _ _ _ _ _ _ _ _ BS OS LS SB SC ST)) as W0.
      destruct (bcWait_bisim_inj _ _ _ _ (bisim_trans _ _ _ (bisim_symm _ _ W0) BW)) as [_ EX].
      symmetry. exact EX.
Qed.

(** While the overlap component is in switchCurr, a waiting broadcaster with time left has
broadcast since nextSince began.*)
Local Lemma switchCurr_bcWait_nextSince_time n m m' t x i (p : reachableProtNet n) :
  nextSince m t i n p -> switchCurrStateNet i n -> bcWaitStateNet m' x i n -> zeroTime < x ->
  period m' - x <= t.
Proof.
  intro NS. revert m' x. induction NS as [a i n n' p w l t t' x y PE OR OW
    | a t i n n' p w NS IH NSS | d t i n n' p w NS IH]; intros m' x0 SC BW XP.
  - exfalso. pose proof (overlap_states_bisim_net _ _ _ _ OW SC) as BT. ovWait_bisim_contra BT.
  - destruct (switchCurr_prev_net_bcWait _ _ _ _ _ _ p w SC BW) as [SC0 | Z];
      [ | subst x0; simpl in XP; lra].
    destruct (bcWait_bktrk_net _ _ _ _ _ _ p w BW) as [BW0 | [Z | [l [_ [X _]]]]].
    + exact (IH _ _ SC0 BW0 XP).
    + subst x0. simpl in XP. lra.
    + subst x0. pose proof (cond_nonneg (time t)). lra.
  - destruct (reachableProtNet_del_prev _ _ _ _ _ p w SC) as [BS [OS _]].
    assert (SC0 : switchCurrStateNet i n)
      by (apply (overlap_del_bkwd_net switchCurr _ _ _ _ OS w SC); intros m0 e2 e3 e4 B;
          ovWait_bisim_contra B).
    lets BW0 : bcWaitNet_del_bkwd BS XP w BW.
    assert (XP0 : zeroTime < delToTime (x0 +dt+ d))
      by (simpl; simpl in XP; pose proof (cond_pos (delay d)); lra).
    lets IH0 : IH SC0 BW0 XP0. simpl in *. lra.
Qed.

(* If we are in the wait state of the broadcast component with time x,
and we are currSince for time t, then x <= t.*)
Theorem bcWait_currSince_time (n : Network) (m : Mode) (x t: Time)
  (i : nat) (p : reachableProtNet n) :
  bcWaitStateNet m x i n -> zeroTime < x -> currSince m t i n p -> period m - x <= t.
(**Proof: Induction on currSince.
Base case: x = period m, so <= t is trivial.
Discrete inductive: x and t preserved so I.H. carries forth.
Delay inductive: x decreases, t increases, so I.H. is more than enough.
*)
Proof.
  intros BW XP CS. revert x BW XP.
  induction CS as [a t i n n' p w NS SC SL | a t i n n' p w CS IH CM | d t i n n' p w CS IH];
    intros x0 BW XP.
  - destruct (bcWait_bktrk_net _ _ _ _ _ _ p w BW) as [BW0 | [Z | [l [_ [X _]]]]].
    + eapply switchCurr_bcWait_nextSince_time; eassumption.
    + subst x0. simpl in XP. lra.
    + subst x0. pose proof (cond_nonneg (time t)). lra.
  - destruct (bcWait_bktrk_net _ _ _ _ _ _ p w BW) as [BW0 | [Z | [l [_ [X _]]]]].
    + exact (IH _ BW0 XP).
    + subst x0. simpl in XP. lra.
    + subst x0. pose proof (cond_nonneg (time t)). lra.
  - destruct (reachableProtNet_del_prev _ _ _ _ _ p w BW) as [BS _].
    lets BW0 : bcWaitNet_del_bkwd BS XP w BW.
    assert (XP0 : zeroTime < delToTime (x0 +dt+ d))
      by (simpl; simpl in XP; pose proof (cond_pos (delay d)); lra).
    lets IH0 : IH BW0 XP0. simpl in *. lra.
Qed.

(* If we are in the wait state of the broadcast component, and the clock value is non-zero,
then a message containing the mode in question and some position was sent exactly
(period m - x) time units ago.*)
Theorem bcWait_sent (n : Network) (m : Mode) (x : Time)
  (i : nat) (p : reachableProtNet n) :
  bcWaitStateNet m x i n -> zeroTime < x ->
  exists l q,
  sent [baseMode m, basePosition l] (minusTime (period m) x q) i n p.
  intros. gen x.
  (*Induction on p.*)
  induction p; intros.
  (*The base case fails because we know all entities are sleeping to begin with.*)
  false. eapply initial_not_bcWait_net. apply i0. apply H.
  (*The discrete inductive case follows from the theorem (bcWait_bktrk_net).*)
  assert (x <> zeroTime) as Q. unfold not. intro F. rewrite F in H0.
  contradiction (Rlt_irrefl zeroTime).
  lets BB : bcWait_bktrk_net p s H. decompOr3 BB W1 W2 W3.
  apply IHp in W1. decompEx2 W1 l q V. exists l q. constructor. assumption.
  assumption. contradiction (Q W2). invertClearAs2 W3 l L.
  andflat Y. rewrite <- Y1. exists l (Rle_refl x). my_applys_eq Y2.
  timering.
  (*The delay inductive case follows by an application of I.H. and then the delay
  constructor for sent.*)
  lets BSP : reachableProtNet_del_prev p s H. destruct BSP as [BS _].
  lets BD : bcWaitNet_del_bkwd BS H0 s H. assert (zeroTime < x +dt+ d) as ZL.
  apply Rplus_lt_weaken_rl. timeNonneg. simpl.
  delPos. lets IH : IHp BD ZL. decompEx2 IH l q SE. assert (x <= period m) as q0.
  simpl in q. eapply Rplus_le_weaken_lr. apply q. apply Rlt_le. delPos. exists l q0.
  eapply sentDel in SE. my_applys_eq SE. timering. Qed.


(* Let's say an entity has been broadcasting in the current mode m since t time units ago.
Then for any t' < t, we can assert that a message was sent containing the mode in
question m and some position l0 within the window t' and t' + period m. We also know
that the message was sent at most t units ago.*)
Theorem currSince_periodic_sent (n : Network) (m : Mode) (t t' : Time)
  (i : nat) (p : reachableProtNet n) :
  currSince m t i n p -> ~ failSafe m -> t' < t ->
  exists t'' l, t' < (time t'')  /\ t'' <= t' + period m /\ t'' <= t /\
  sent [baseMode m, basePosition l] t'' i n p. 
  (*Let us start with a little attempt at a sketch of what is to be proven:

  currSince-------------t------------
    [  period m )--------t'----------
        sent------------t''----------  

  Now we proceed by induction on currSince.*)
  intros H NF H0. generalize dependent t'. induction H; intros.
  (*In the base case, we have that the previous state was nextSince. In which case we
  apply (nextSince_periodic_sent) and the discrete sent constructor and we're done.*)
  addHyp (nextSince_periodic_sent n m t t' i p H H2). decompose [ex] H3.
  rename x into t''. rename x0 into l. exists t''. exists l. decompose [and] H5.
  clear H5. repeat (split; try assumption). constructor. assumption.
  (*The discrete inductive case is easy: apply I.H. and then discrete constructor for sent.*)
  apply IHcurrSince in H1. decompose [ex] H1. clear H1. decompose [and] H3.
  clear H3. rename x into t''. rename x0 into l. exists t''. exists l.
  clear IHcurrSince. repeat (split; try assumption). constructor. assumption.
  (*Which leaves the delay Here we do a case analysis on d <= t' or t' < d.*)
  addHyp (Rle_or_lt d t'). invertClear H1.
  (*In the former case, we can show then that t' = t'' + d for some t''.*)
  assert (exists t'', nonneg t' = (time t'') + d). apply RlePlusExistsR in H2.
  invertClear H2. rename x into t''. invertClear H1. rewrite Rplus_comm in H2.
  exists (mkTime (mknonnegreal t'' H3)). apply H2. invertClear H1. rename x into t''.
  (*Now, we also know t' < t + d, so t'' < t*)
  assert (t'' < t). rewrite H3 in H0. simpl in H0. eapply Rplus_lt_reg_r in H0.
  assumption.
  (*So we can apply the I.H. for t'' and the previous state*)
  apply IHcurrSince in H1. clear IHcurrSince. decompose [ex] H1. clear H1.
  rename x into u. rename x0 into l. decompose [and] H5. clear H5.
  (*So our existential becomes u + d*)
  exists (u +dt+ d). exists l.
  (*Now we need to show inequality the sub-cases of our goal by a bit of algebraic manipulation*)
  split. rewrite H3. apply Rplus_lt_compat_r. assumption. split. rewrite Rplus_comm.
  rewrite H3. rewrite <- Rplus_assoc. apply Rplus_le_compat_r. rewrite Rplus_comm.
  assumption. split. apply Rplus_le_compat_r. assumption.
  (*Then apply the sent delay constructor and we're done.*)
  constructor. assumption.
  (*Now all that remains is the delay case where t' < d. Well we know that the previous state
  was bcWait m (x + d)*)
  addHyp (currSince_del_bcWait n n' m t i d p w H NF). invertClear H1.
  (*So by (bcWait_sent) we get sent <m, l> (period m - (x + d)) for the previous case*)
  assert (zeroTime < (delToTime (x +dt+ d))). simpl. replace 0 with (0 + 0).
  apply Rplus_le_lt_compat. timeNonneg. delPos. ring.
  addHyp (bcWait_sent n m (x +dt+ d) i p H3 H1). decompose [ex] H4. clear H4.
  rename x1 into Q. rename x0 into l.
  (*So for the current case our existential is period m - x*)
  assert (x <= period m). simpl in Q. eapply Rplus_le_weaken_lr. apply Q.
  apply Rlt_le. delPos. exists (minusTime (period m) x H4). exists l. split.
  (*Now since t' < d < period m - x, then t' < period m - x.*)
  eapply Rlt_le_trans. apply H2. simpl. simpl in Q. apply Rplus_le_swap_lr.
  rewrite Rplus_comm. assumption. split.
  (*But we also clearly have that period m - x <= t' + period m*)
  simpl. rewrite Rplus_comm.
  apply Rminus_le_weaken_lr. timeNonneg. apply Rplus_le_weaken_rr. timeNonneg.
  apply Rle_refl. split. simpl. addHyp (bcWait_currSince_time n m (x +dt+ d) t i p H3 H1 H).
  simpl in H5. apply Rminus_le_swap_lr. eapply Rle_trans;[ |apply H5].
  apply Req_le. ring.
  (*So now by the delay constructor of sent, we get sent <m, l> (period m - x) for the current
  state:
  currSince-------------t------------|---------------d-------------|
                          [  period m )------------t'------------|
                             sent---(period m - x)---------------|
  and we're done.*)
  replace (minusTime (nonneg (time (period m))) (nonneg (time x)) H4)
  with (delToTime (minusTime (nonneg (time (period m)))
  (nonneg (time (delToTime (x +dt+ d)))) Q +dt+ d)).
  constructor. assumption. apply timeEqR. simpl. ring. Qed.

(*If an entity in position l is currSince m t, then it has delivered a message <m, l0>
to a sufficient radius r and this happened t - mL time units ago. Also, l0 differs from
l by at most Smax*t.*)
Theorem currSince_fst_deliv_suff (n : Network) (m : Mode) (t : Time)
  (i : nat) (l : Position) (p : reachableProtNet n) :
  currSince m t i n p -> inPosNet l i n ->
  exists q,
  let s := (Rplus_lt_weaken_lr msgLatency (Rmax adaptNotif transMax) t q
  maxAnTrans_positive) in
  let s' := Rlt_le msgLatency t s in
  exists r l0 l1,
  delivered ([-[baseMode m, basePosition l0], l1, r-]) (minusTime t msgLatency s') i n p /\ 
  sufficient m r /\ dist2d l l0 <= speedMax*t. 
  (*Induction on currSince.*)
  intro. generalize dependent l. induction H; intros.
  (*In the base case, we have that the previous entity was nextSince m t and in
  switchCurrState. Then by (nextSince_switchCurr_lower) we would get
  that mL + max AN trans < t.*)
  addHyp (nextSince_switchCurr_lower n m i t p H H0).
  (*From this we easily obtain mL + AN < t.*)
  assert (msgLatency + adaptNotif < t). eapply Rle_lt_trans;[ |apply H3].
  apply Rplus_le_compat. apply Rle_refl. apply Rmax_l.
  (*Also, it is clear by the discrete nature of the transition in this case that the
  position is preserved.*)
  addHyp (inPos_pres_disc n n' a l i w). rewrite <- H5 in H2.
  (*Hence by (nextSince_fst_deliv_suff) we have delivered <m, l0> r (t - mL) i n p /\ 
  sufficient m r /\ |l - l0| <= Smax*t for some r and l0.*)
  addHyp (nextSince_fst_deliv_suff n t m i l p H H2 H3). cbv zeta in H6.
  decompose [ex] H6. clear H6. rename x into l0. rename x0 into l1. rename x1 into r.
  decompose [and] H7. clear H7. exists H3. exists r. exists l0. exists l1.
  repeat (split; try assumption). 
  (*This closely resembles our goal, the only difference being the
  delivered <m, l0> r (t - mL) i n p instead of delivered <m, l0> r (t - mL) i n' p'.
  This last touch is shown by the application of the discrete delivered constructor, and
  we're done with this case.*)
  constructor. assumption.
  (*The discrete inductive case is almost identical to the base case: backwards preservation of
  position, apply I.H., apply discrete constructor on delivered.*)
  addHyp (inPos_pres_disc n n' a l i w). rewrite <- H2 in H1.
  apply IHcurrSince in H1. clear IHcurrSince. cbv zeta in H1.
  decompose [ex] H1. clear H1. rename x into q. rename x0 into r. rename x1 into l0.
  rename x2 into l1. decompose [and] H4. clear H4. exists q. exists r. exists l0. exists l1.
  repeat (split; try assumption). constructor. assumption.
  (*The delay case is a little more complicated. We apply the result (inPos_del_bound_bkwd)
  to show that the previous state was inPosNet l1 i n, for some l1 with |l - l1| <= Smax*d.*)
  addHyp (inPos_del_bound_bkwd n n' d l i H0 w). invertClear H1. rename x into l0.
  invertClear H2. 
  (*Then we apply the inductive hypothesis and tidy up a bit.*)
  apply IHcurrSince in H1. clear IHcurrSince. cbv zeta in H1. decompose [ex] H1.
  clear H1. rename x0 into r. rename x1 into l1. rename x2 into l2.
  decompose [and] H4. clear H4. 
  (*Now, we have mL + max AN trans < t, so clearly mL + max AN trans < t + d*)
  assert (msgLatency + Rmax adaptNotif transMax < t +dt+ d) as q. apply Rplus_lt_weaken_rr.
  apply Rlt_le. delPos. assumption.
  (*Now we can use this last assertion as our existential and carry on with the goal.*)
  exists q. exists r. exists l1. exists l2. split.
  (*The proof of delivered carries over by the delay delivered constructor.*)
  replace (minusTime (nonneg (time (delToTime (t +dt+ d)))) (nonneg (time msgLatency))
  (Rlt_le (nonneg (time msgLatency)) (nonneg (time (delToTime (t +dt+ d))))
  (Rplus_lt_weaken_lr (nonneg (time msgLatency))
  (Rmax (nonneg (time adaptNotif)) (nonneg (time transMax)))
  (nonneg (time (delToTime (t +dt+ d)))) q maxAnTrans_positive))) with
  (delToTime (minusTime (nonneg (time t)) (nonneg (time msgLatency))
  (Rlt_le (nonneg (time msgLatency)) (nonneg (time t))
  (Rplus_lt_weaken_lr (nonneg (time msgLatency))
  (Rmax (nonneg (time adaptNotif)) (nonneg (time transMax)))
  (nonneg (time t)) x maxAnTrans_positive)) +dt+ d)). constructor. assumption. apply timeEqR. simpl. ring.
  (*The sufficiency of the message is preserved.*)
  split. assumption.
  (*The bound on the distance then is shown by the triangle inequality. Elaborating on this last
  point, we want to show |l - l0| <= Smax*(t + d). We have both that |l - l1| <= Smax*d and
  |l1 - l0| <= Smax*t. The triangle inequality also gives us
  that |l - l0| <= |l - l1| + |l1 - l0|. So we get our result by adding the inequalities
  and transitivity.*)
  eapply Rle_trans. eapply dist_tri_ineq. simpl. rewrite Rmult_plus_distr_l.
  rewrite Rplus_comm. apply Rplus_le_compat. apply H6. rewrite distSymmetric in H3.
  apply H3. Qed.

(*If an entity in position l is currSince m t, then it has delivered a message <m, l0> to a
sufficient radius r and this happened t' time units ago, with t' < t in the pre delivery
interval of m and the distance between the sent position and the current position being no
more than Smax*(mL + t').*)
Theorem pre_del_suff (n : Network) (m : Mode) (t : Time)
  (i : nat) (l : Position) (p : reachableProtNet n) :
  currSince m t i n p -> inPosNet l i n -> ~failSafe m ->
  exists t' r l0 l1,
  delivered ([-[baseMode m, basePosition l0], l1, r-]) t' i n p /\ 
  sufficient m r /\ t' [:] (preDeliveredInterval m) /\ t' < t /\
  dist2d l l0 <= speedMax*(msgLatency+ t'). intros.
  match goal with [ H : ~failSafe m |- _ ] => rename H into Q end.
  (*Let us first recall the definition of
  Ipd = (max AN trans, max AN trans + period m + trans m]).*)  
  remember (preDeliveredInterval m) as h. unfold preDeliveredInterval in Heqh.
  (*Let u = mL + max AN trans + period m + trans m. Then we can do a case analysis on
  t <= u or u < t.*)
  remember (msgLatency + Rmax adaptNotif transMax + period m + trans m) as u.
  addHyp (Rle_or_le t u). invertClear H1.
  (*Case t <= u: Well, we can show by (currSince_fst_deliv_suff) that there is a sufficient
  message delivered at t' = t - mL and some position l0 is sent in that message such
  that |l - l0| <= Smax*(mL + t').*)
  addHyp (currSince_fst_deliv_suff n m t i l p H H0). simpl in H1. decompose [ex] H1.
  clear H1. decompose [and] H4. clear H4. rename x0 into r. rename x1 into l0.
  rename x2 into l1. remember (minusTime t msgLatency (Rlt_le msgLatency t
  (Rplus_lt_weaken_lr msgLatency (Rmax adaptNotif transMax) t x maxAnTrans_positive)))
  as t'.
  foldDist l l0 H6. assert (nonneg t = t' + msgLatency). rewrite Heqt'. simpl. ring.
  rewrite H3 in H6. rewrite Rplus_comm in H6.
  (*By the positivity of mL, it is easy to show t' < t.*)
  assert (t' < t). rewrite H3. apply Rlt_plus_r.
  apply msgLatency_positive.
  (*So now we can apply t', r, l0, and l1 as our existential witnesses and it just
  remains to show that t' : Ipd m.*)
  exists t' r l0 l1. split. assumption. split. assumption. split;[ |split;assumption].
  rewrite Heqh. replace (nonneg (time t')) with (nonneg (time t') +
  nonneg (time msgLatency) - nonneg (time msgLatency));[ | ring]. split.
  (*Well, since by (currSince_lower_bound) we have that mL + max AN trans < t,
  then max AN trans < t - mL = t', which is our lower bound done.*)
  addHyp (currSince_lower_bound n t m i p H). apply Rplus_lt_swap_ll in H7.
  rewrite H3 in H7. simpl. assumption.
  (*Also, since t <= u = mL + max AN trans + period m + trans m, then
  t - mL <= max AN trans + period m + trans m,which is our upper bound done.
  Case closed.*)
  simpl. rewrite Hequ in H2. rewrite Rplus_assoc in H2. rewrite Rplus_assoc in H2.
  apply Rplus_le_swap_rl in H2. rewrite H3 in H2. rewrite Rplus_assoc. assumption.
  (*Case u < t. Well we can easily show mL + max AN trans + trans m < t.
  We show this by transitivity via u*)
  assert (nonneg (time msgLatency) +
  Rmax (nonneg (time adaptNotif)) (nonneg (time transMax)) + nonneg (time (trans m)) < t).
  eapply Rlt_le_trans;[ |apply H2]. rewrite Hequ. apply Rplus_lt_compat_r.
  rewrite Rplus_assoc. repeat (apply Rplus_lt_compat_l). apply Rlt_plus_r.
  apply period_positive.
  (*so by (currSince_periodic_sent) we have that there was a sent message <m, l0> at a time
  t' within the window (mL + max AN trans + trans m, mL + max AN trans + period m + trans m]
  and t' <= t ($).*)
  remember (msgLatency +t+ (timeMax adaptNotif transMax) +t+ trans m) as w.
  assert (nonneg (time msgLatency) + Rmax (nonneg (time adaptNotif))
  (nonneg (time transMax)) + nonneg (time (trans m)) =
  nonneg ((msgLatency +t+ timeMax adaptNotif transMax) +t+ trans m)). simpl.
  ring. rewrite H3 in H1. rewrite <- Heqw in H1.
  addHyp (currSince_periodic_sent n m t w i p H Q H1). decompose [ex] H4.
  clear H4. decompose [and] H6. clear H6. rename x0 into l0. rename x into t'.
  assert (t' <= u). rewrite Hequ. eapply Rle_trans. apply H7. rewrite Heqw.
  rewrite <- H3. rewrite Rplus_assoc. rewrite Rplus_comm. rewrite Rplus_assoc.
  rewrite Rplus_comm. apply Rplus_le_compat_r. rewrite Rplus_comm. apply Rle_refl.
  rewrite Hequ in H6.
  (*By (sent-pos_bound) we can establish that |l - l0| <= Smax*t' (@).*)
  addHyp (sent_pos_bound n m t' i l l0 p H9 H0).
  (*Then by (sent_delivered) we know that this message was delivered to some radius r
  at time t'' = t' - mL ($$)*)
  assert (msgLatency < t'). eapply Rle_lt_trans;[ |apply H4]. rewrite Heqw.
  rewrite <- H3. rewrite Rplus_assoc. apply Rle_plus_r. apply Rle_zero_plus.
  rewrite <- timeMax_RMax. timeNonneg.
  timeNonneg.
  addHyp (sent_delivered n [baseMode m, basePosition l0] t' i p H9 H10).
  decompose [ex] H11. clear H11. rename x0 into l1. rename x into r. 
  remember (minusTime (nonneg (time t')) (nonneg (time msgLatency))
  (Rlt_le (nonneg (time msgLatency)) (nonneg (time t')) H10)) as t''.
  (*We can show that t'' is within the window
  (max AN trans + trans m, max AN trans + period m + trans m]) (@@)*)
  assert ((Rmax adaptNotif transMax) + trans m < t'').
  rewrite Heqt''. simpl. apply Rplus_lt_swap_ll. rewrite <- Rplus_assoc.
  rewrite H3. rewrite <- Heqw. assumption. 
  assert (t'' <= (Rmax adaptNotif transMax) + period m + trans m).
  rewrite Heqt''. simpl. apply Rplus_le_swap_rl. repeat rewrite <- Rplus_assoc.
  assumption.
  (*It is clear then that t'' is also within the window Ipd m, since the window
  mentioned above is contained within Ipd m*)
  assert (t'' [:] preDeliveredInterval m). split;simpl.
  eapply Rle_lt_trans;[ | apply H11]. apply Rle_plus_r. timeNonneg.
  assumption.
  (*Now, since from ($) t' <= t, then t'' < t, by ($$) and the
  positivity of mL*)
  assert (t'' < t). rewrite Heqt''. simpl. eapply Rlt_le_trans;[ |apply H5].
  apply Rplus_lt_swap_rr. apply Rlt_plus_r. apply msgLatency_positive.
  (*Also, rearranging ($$) we get t' = mL + t''*)
  assert (nonneg t' = msgLatency + t''). rewrite Heqt''. simpl. ring.
  (*Substituting into our earlier result (@) we get |l - l0| <= Smax*(mL + t'').*)
  rewrite H16 in H8.
  (*Now let's apply t'', r, l0 and l1 as our existential witnesses and prune the goal.*)
  exists t'' r l0 l1. rewrite Heqh. repeat (split;try assumption).
  (*We have now shown every sub-goal except the sufficiency of the delivered message.
  It can be shown that the coverage r must be sufficient for the mode m by assuming
  otherwise and proving a contradiction.*)
  addHyp (suffDec m r). appDisj H17. assumption. 
  (*Well, it is clear from (@@) that AN < t''*)
  assert (adaptNotif < t''). eapply Rle_lt_trans;[ |apply H11].
  apply Rplus_le_weaken_rr. timeNonneg. apply Rmax_l.
  (*We have already shown that t'' < t so by (NARInsuff::insuff_react), we get that
  we are tfs m (t'' - AN).*)
  addHyp (insuff_react n m l0 l1 r t t'' i p H H13 H17 H15 n0 Q).
  (*Now, by (tfs_bound), this would imply t'' - AN <= trans m.*)
  decompExAnd H18 x LT TF. lets TB : tfs_bound TF.
  assert (minusTime t'' adaptNotif (Rlt_le adaptNotif t'' H17) <= trans m) as C1.
  eapply Rle_trans. apply LT. assumption.
  (*However, we also have by (@@) that max AN trans + trans m < t'' and so
  AN + trans m < t''*)
  assert (adaptNotif + trans m < t''). eapply Rle_lt_trans;[ |apply H11].
  apply Rplus_le_compat_r. apply Rmax_l.
  (*and so trans m < t'' - AN.*)
  simpl in C1. apply Rplus_lt_swap_ll in H18.
  (*Hence we arrive at a contradiction, which is that t'' - AN < t'' - AN*)
  apply False_ind. apply (Rlt_irrefl (t'' - adaptNotif)). eapply Rle_lt_trans.
  apply C1. assumption. Qed.
  (*So we must accept that the broadcast range was sufficient. This concludes the proof of
  all our sub-goals.*)

End NARTop.
