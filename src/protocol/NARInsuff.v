(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

(*Require Import Reals.
Require Import List.*)
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lra.

Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.NARMisc.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.ProtocolBridge.
 
(*TIDY*)

(*TOGO: NARMisc*)
Lemma tfs_state_rel i n (p : reachableProtNet n) :
  tfsStateNet i n -> exists m t, tfs m t i n p.
  Admitted. (*4*)
  (*Proof: Induction on reachable.*)

(*TOGO: NARMisc?*)
(* begin helpers for tfs_currModeNet *)
Ltac tfs_currModeNet_close :=
  unfold bcWaitState, sleepingState, bcReadyState, dormantState, ovWaitState,
    ovReadyState, switchBcState, switchCurrState, switchListenState, tfsStartState,
    tfsNextState, tfsCurrState, tfsBcState, tfsListenState, initState, ovAbortState,
    listeningState, rangeBadState, currOKState, abortOvlpState, badOvlpState,
    currCompState, pausedState, gotMsgState, gotRangeState, currEqState, nextEqState,
    currPincCheckState, nextPincCheckState in *;
  match goal with
  | [V : ProcEquiv.bisimulation ?p ?x, V1 : ProcEquiv.bisimulation ?p ?y |- False] =>
    let BT := fresh "BT" in
    assert (ProcEquiv.bisimulation x y) as BT by
      (eapply ProcEquiv.bisim_trans; [apply ProcEquiv.bisim_symm; exact V | exact V1]);
    unfold bcWait, sleeping, bcReady, dormant, init, ovWait, ovReady, switchBc,
      switchCurr, switchListen, tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen, ovAbort,
      listening, checkRange, rangeBad, currEq, badOvlp, currOK, nextEq, abortOvlp,
      gotMsg, gotRange, currPincCheck, currComp, nextPincCheck, paused in BT;
    first [solve [bisim_contra BT] |
      apply ProcEquiv.bisim_symm in BT; solve [bisim_contra BT]]
  end.
(* end helpers *)

Lemma tfs_currModeNet m1 m2 t i n p : tfs m1 t i n p ->
  currModeNet m2 i n -> ~failSafe m2 -> m1 = m2.
Proof.
  intro H. induction H as [i n p TS CM | a t i n n' p w TF IH TSN | d t i n n' p w TF IH];
    intros C NF.
  - apply currMode_ent_ex in CM. apply currMode_ent_ex in C.
    destruct CM as [e [E1 E2]]. destruct C as [e' [E1' E2']].
    pose proof (entInNetUnique _ _ _ _ E1 E1') as EQ. subst e'. congruence.
  - destruct (currMode_pres_bkwd n n' a m2 i w C) as [x X].
    destruct (eqDecMode x m2) as [EQ | NEQ].
    + subst. apply IH; assumption.
    + destruct (currModeNet_switch_states n n' a x m2 i p w X C NEQ)
        as [[SC SL] | [TC TB]].
      * exfalso.
        destruct SL as [e E I]. destruct TSN as [e' E' I'].
        pose proof (entInNetUnique _ _ _ _ I I') as EQ. subst e'.
        destruct E as [q l h k P]. inversion P; subst.
        inversion E'; subst.
        match goal with Hq : tfsStateProt _ |- _ => inversion Hq; subst end.
        match goal with Hq : tfsState _ |- _ => inversion Hq; subst end;
          tfs_currModeNet_close.
      * exfalso. apply NF. destruct TB as [e E I].
        apply currMode_ent_ex in C. destruct C as [e' [I' C']].
        pose proof (entInNetUnique _ _ _ _ I I') as EQ. subst e'.
        rewrite <- C'. apply tfsBc_failSafe; [ | exact E].
        exact (reachable_net_ent _ _ _ (reachNetDisc n n' a p w) I).
  - apply IH; [ | assumption].
    apply (proj2 (currModeNet_del_pres n n' d m2 i w)). assumption.
Qed.
(**Proof: induction on tfs. The first base follows from the definition of
tfs. The discrete inductive case follows by application of I.H. and use
of the mode-swith-states(exact name?) theorem to eliminate all states
except tfsCurr->tfsBc. For this, it can be shown that the curr mode
is fail safe in the derivative, contradicting our hypothesis. The delay
inductive case follows by I.H. and a preservation theorem (name?) for
currModeNet over a delay*)

(*-TIDY*)

(***************************** Basic Results *****************************)

(* begin helpers for currModeNet_notifBad_pres_bkwd *)
Ltac currModeNet_notifBad_pres_bkwd_close :=
  unfold bcWaitState, sleepingState, bcReadyState, dormantState, ovWaitState,
    ovReadyState, switchBcState, switchCurrState, switchListenState, tfsStartState,
    tfsNextState, tfsCurrState, tfsBcState, tfsListenState, initState, ovAbortState,
    listeningState, rangeBadState, currOKState, abortOvlpState, badOvlpState,
    currCompState, pausedState, gotMsgState, gotRangeState, currEqState, nextEqState,
    currPincCheckState, nextPincCheckState in *;
  match goal with
  | [V : ProcEquiv.bisimulation ?p ?x, V1 : ProcEquiv.bisimulation ?p ?y |- False] =>
    let BT := fresh "BT" in
    assert (ProcEquiv.bisimulation x y) as BT by
      (eapply ProcEquiv.bisim_trans; [apply ProcEquiv.bisim_symm; exact V | exact V1]);
    unfold bcWait, sleeping, bcReady, dormant, init, ovWait, ovReady, switchBc,
      switchCurr, switchListen, tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen, ovAbort,
      listening, checkRange, rangeBad, currEq, badOvlp, currOK, nextEq, abortOvlp,
      gotMsg, gotRange, currPincCheck, currComp, nextPincCheck, paused in BT;
    first [solve [bisim_contra BT] |
      apply ProcEquiv.bisim_symm in BT; solve [bisim_contra BT]]
  end.

Lemma currModeNet_notifBad_pres_bkwd_paused i n :
  pausedStateNet i n -> notifBadPathNet i n -> False.
Proof.
  intros P N. destruct P as [e E1 I1]. destruct N as [e' E2 I2].
  pose proof (entInNetUnique _ _ _ _ I1 I2) as EQ. subst e'.
  destruct E1 as [q l h k P]. inversion P as [p1 p2 p3 S]. subst.
  inversion E2; subst.
  - match goal with H : rangeBadStateProt _ _ |- _ => inversion H; subst end.
    currModeNet_notifBad_pres_bkwd_close.
  - match goal with H : badOvlpStateProt _ |- _ => inversion H; subst end.
    currModeNet_notifBad_pres_bkwd_close.
Qed.
(* end helpers *)

Lemma currModeNet_notifBad_pres_bkwd m i n n' a
  (rn : reachableProtNet n) (w : n -NA- a -NA> n') :
  currModeNet m i n' -> notifBadPathNet i n ->
  ~failSafe m ->
  currModeNet m i n \/
  exists t, tfs m t i n' (reachNetDisc n n' a rn w).
Proof.
  intros U U0 U1.
  destruct (currMode_pres_bkwd n n' a m i w U) as [x H].
  destruct (eqDecMode x m) as [EQ | NEQ].
  - subst. left. assumption.
  - destruct (currModeNet_switch_states n n' a x m i rn w H U NEQ) as [[SC SL] | [TC TB]].
    + exfalso. apply (currModeNet_notifBad_pres_bkwd_paused i n); [ | assumption].
      apply (proj2 (paused_switch_net n i rn)).
      destruct SC as [e E I]. destruct E as [q l h k P]. destruct P as [p1 p2 p3 S].
      econstructor; [ | exact I]. constructor. constructor. apply switCurSt. exact S.
    + exfalso. apply U1.
      destruct TB as [e E I].
      apply currMode_ent_ex in U. destruct U as [e' [I' C']].
      pose proof (entInNetUnique _ _ _ _ I I') as EQ. subst e'.
      rewrite <- C'. apply tfsBc_failSafe; [ | exact E].
      exact (reachable_net_ent _ _ _ (reachNetDisc n n' a rn w) I).
Qed.

Lemma currEq_eq_badOvlp_net m m'' i n :
  m = m'' -> currEqStateNet m m'' i n -> badOvlpStateNet i n.
Proof.
  intros E U. destruct U as [e E1 E2]. destruct E1 as [q l h k P].
  destruct P as [p1 p2 p3 S].
  econstructor; [ | exact E2]. constructor. constructor.
  eapply currEq_cond_true; eassumption.
Qed.

(***************************** More Complex Results *****************************)

(*A delay of at most the timestamp t just ages an incoming notification by d. Unlike
(Basics::incomingNetNotif_del), this needs nothing about the listener, so it holds for
any v.*)
Local Lemma incomingNetNotif_del_le (n n' : Network) (d : Delay) (v : list BaseType)
  (t : Time) (i : nat) (q : d <= t) :
  n -ND- d -ND> n' -> incomingNetNotif v t i n ->
  incomingNetNotif v (minusTime t d q) i n'.
Proof.
  introz U. destruct U0.
  link_netentdelfwd_tac e' Y. destr_ent_inter e' p' l' k' li' lo' ln'.
  link_entinterdel_tac Y. inversion_clear Y1.
  econstructor. apply Y. eapply notifList_del_le. apply H3. assumption.
Qed.

(*If a message was delivered at a time less than AN ago, then a notification of that
message's delivery is enqueued with time stamp AN - t. *)
Theorem delivered_incomingNetNotif (n : Network) (v : list BaseType) (r : Distance)
  (l : Position) (t : Time) (i : nat) (p : reachableProtNet n) :
  delivered ([-v, l, r-]) t i n p -> forall q : t < adaptNotif,
  incomingNetNotif ((baseDistance r)::v) (minusTime adaptNotif t (Rlt_le t adaptNotif q)) i n.
  intros H q.
  (**Proof: Induction on delivered.*)
  induction H.
  (*The base case enforces an output of v to r by i. By looking at the semantics,
  we can see that this is only possible when the notification list of entity i also
  buffers r::v with timestamp AN. Hence we have incomingNetNotif r::v AN i n, which is our
  goal because t = 0.*)
  lets OI : outNet_incomingNetNotif w. my_applys_eq OI. apply timeEqR. simpl. ring.
  (*In the discrete inductive case, we have by I.H. that incomingNetNotif r::v (AN - t) i n*)
  lets IH : IHdelivered q. clear IHdelivered.
  (*Also by (Basics::incomingNetNotif-disc-pres) we get incomingNetNotif r::v (AN - t) i n'.*)
  lets ID : incomingNetNotif_disc_pres w IH. apply ID. apply RltMinusBothSides. assumption.
  (*So we're left with the delay inductive case. Well, if t + d < AN, then t < AN*)
  assert (t < adaptNotif) as Q. eapply Rplus_lt_weaken_lr. apply q. apply Rlt_le. delPos.
  (*So by IH incomingNetNotif r::v (AN - t) i n.*)
  lets IH : IHdelivered Q. clear IHdelivered.
  (*Since t + d < AN, the delay d is at most AN - t, so by (incomingNetNotif_del_le) we
  have incomingNetNotif r::v (AN - t - d) i n' which is the same as incomingNetNotif r::v
  (AN - (t + d)) i n and we're done.*)
  assert (d <= minusTime adaptNotif t (Rlt_le t adaptNotif Q)) as DL.
  simpl. simpl in q. lra.
  lets Q2 : incomingNetNotif_del_le DL w IH.
  my_applys_eq Q2. apply timeEqR. simpl. ring. Qed.


Theorem insuff_incomingNotif_abort (n n' : Network) (a : ActDiscNet) (m : Mode)
  (r : Distance) (l : Position) (i : nat) : 
  reachableProtNet n -> nextModeNet m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
  notifAbortPathNet i n'. Admitted. (*3*)
(**Proof: Much like Basics::outgoing_timeout_disc. We case analyse the action a.
For the cases where a is either input, output or ignore, we can show that
incomingNetNotif is preserved (...linking theorems / theorems on timed lists...),
and we have our LHS. In the remaining case, a is a tau action. Then we can show
that either incomingNetNotif <r, m, l> 0 i n' or the tau is the result of an output
of <r, m, l> by the interface on the channel AN and an input by the process on
this channel. Then by the base case of notifAbortPath, we have that
notifAbortPath m r i n', giving us the RHS of the goal, and we're done.

Idea: Standardised proof method? Destruct everything right down to timed lists of interface,
then show the notif lists are either equal or there's a transition from one to the other.
Then show that only such a transition, with the arguments of the buffered message,
will cause it to leave the list. But in that case, you have a case for the notifAbort path.
So that's it.*)

Theorem nextSince_next (n : Network) (m : Mode) (t : Time) (i : nat) (p : reachableProtNet n) : 
  nextSince m t i n p -> nextModeNet m i n.
Proof. intro U. exact (ComhCoq.protocol.NARMisc.nextSince_next _ _ _ _ _ U). Qed.
(**Proof: As detailed above*)

(*If an entity is on the notification abort path, and a
discrete transition happens, then in the next state it is either still on the
notification abort path, or it is not in a nextSince state.*)

Theorem notifAbort_not_nextSince (n n' : Network)
  (a : ActDiscNet) (i : nat) (rn : reachableProtNet n) : 
  notifAbortPathNet i n -> n -NA- a -NA> n' ->
  notifAbortPathNet i n' \/ ~nextSinceStateNet i n'.
Proof.
  intros U W.
  destruct U as [e E I].
  destruct (link_net_ent_disc_fwd n n' e i a W I) as [e' [I' [EQ | [b ST]]]].
  { subst e'. left. econstructor; eassumption. }
  assert (R : reachableProtEnt e) by (eapply reachable_net_ent; eassumption).
  destruct e as [p l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ ST)
    as [p1' [p2' [p3' [l' [h' [k' [EQ' [W1 [W2 W3]]]]]]]]].
  subst e'.
  assert (NSN : ~ nextSinceStateEnt ([|p1' $||$ p2' $||$ p3', l', h', k'|]) ->
    ~ nextSinceStateNet i n')
    by (intros NSE NS; apply NSE; exact (liftEntNet_ent _ _ _ _ NS I')).
  destruct (eqDecProcTerm p3 p3') as [E3 | N3].
  - (* the listener stays *)
    subst p3'.
    inversion E; subst.
    + match goal with [H : rangeBadStateProt _ _ |- _] =>
        inversion H as [? ? ? RB]; subst end.
      destruct (eqDecModeState k k') as [KE | KN].
      * subst k'. left. econstructor; [ | exact I'].
        eapply napRng; [constructor; exact RB | reflexivity | eassumption | eassumption].
      * right. apply NSN. eapply mState_change_not_nextSince_ent; [exact R | | exact KN | exact ST].
        eapply nextMode_unstable. eassumption.
    + match goal with [H : currOKStateProt _ _ |- _] =>
        inversion H as [? ? ? CO]; subst end.
      destruct (eqDecModeState k k') as [KE | KN].
      * subst k'. left. econstructor; [ | exact I'].
        eapply napCuok; [constructor; exact CO | eassumption].
      * right. apply NSN. eapply mState_change_not_nextSince_ent; [exact R | | exact KN | exact ST].
        eapply nextMode_unstable. eassumption.
    + match goal with [H : abortOvlpStateProt _ |- _] =>
        inversion H as [? ? ? AO]; subst end.
      left. econstructor; [ | exact I']. eapply napAbort. constructor. exact AO.
  - (* the listener steps *)
    destruct W3 as [E3 | [b3 T3]]; [contradiction | ].
    inversion E; subst.
    + (* rangeBad: it reads the current mode, which differs from m', into currOK m' *)
      match goal with [H : rangeBadStateProt _ _ |- _] =>
        inversion H as [? ? ? RB]; subst end.
      assert (ACT : forall c, p3 -PA- c -PA> p3' -> entChanAct c).
      { intros c T. destruct (rangeBad_next_act _ _ _ _ T RB) as [m0 [EC _]].
        subst c. left. reflexivity. }
      destruct (triple_disc_ent_chan 2 R ST eq_refl eq_refl ACT) as [E3 | ST3];
        [contradiction | ].
      destruct (ent_disc_proc_read _ _ _ _ _ _ _ _ _ ST3) as [E3 | [c [T [_ [RC _]]]]];
        [contradiction | ].
      destruct (rangeBad_next_act _ _ _ _ T RB) as [m0 [EC CE]].
      destruct (RC m0 EC) as [M0 KE]. subst k'.
      left. econstructor; [ | exact I']. eapply napCuok; [ | eassumption].
      constructor. eapply currEq_cond_false; [ | exact CE]. congruence.
    + (* currOK: with a next mode, it reads it on mNext, into abortOvlp *)
      match goal with [H : currOKStateProt _ _ |- _] =>
        inversion H as [? ? ? CO]; subst end.
      assert (ACT : forall c, p3 -PA- c -PA> p3' -> entChanAct c).
      { intros c T. destruct (currOK_next_act _ _ _ _ T CO) as [[EC _] | [m0 [EC _]]];
          subst c; left; reflexivity. }
      destruct (triple_disc_ent_chan 2 R ST eq_refl eq_refl ACT) as [E3 | ST3];
        [contradiction | ].
      destruct (ent_disc_proc_read _ _ _ _ _ _ _ _ _ ST3)
        as [E3 | [c [T [_ [_ [RN RS]]]]]]; [contradiction | ].
      destruct (currOK_next_act _ _ _ _ T CO) as [[EC _] | [m0 [EC NQ]]].
      * destruct (RS EC) as [NN _]. congruence.
      * destruct (RN m0 EC) as [NM KE]. subst k'.
        left. econstructor; [ | exact I']. eapply napAbort. constructor.
        eapply nextEq_cond_true; [ | exact NQ]. congruence.
    + (* abortOvlp: it outputs on abort, which only the overlap component can take, and
         the overlap component then leaves the nextSince states *)
      match goal with [H : abortOvlpStateProt _ |- _] =>
        inversion H as [? ? ? AO]; subst end.
      assert (TR : forall c, p3 -PA- c -PA> p3' -> c = chanAbort ;! []).
      { intros c T. eapply abortOvlp_listening_track; [exact AO | | exact T].
        eapply abortOvlp_next; eassumption. }
      right. apply NSN. intro NS.
      (* the step is the software's: a component's own step on an entity channel would be
         the listener's on abort, which is not one *)
      inversion ST; subst; try (exfalso; apply N3; reflexivity);
        match goal with
        | [K : p1 $||$ p2 $||$ p3 -PA- tauAct -PA> _ |- _] => idtac
        | [K : p1 $||$ p2 $||$ p3 -PA- _ -PA> _ |- _] =>
            triple_disc_nonTau K; try (exfalso; apply N3; reflexivity);
            match goal with [K3 : p3 -PA- _ -PA> _ |- _] =>
              apply TR in K3; discriminate K3 end
        end.
      match goal with [K : p1 $||$ p2 $||$ p3 -PA- tauAct -PA> _ |- _] =>
        destruct (link_reach_triple_tau _ _ _ _ _ _ K PS) as [c [v CC]] end.
      destruct CC as [[T1 [T2 E0]] | [[T1 [T2 E0]] | [[T1 [T2 E0]] | [[T1 [T2 E0]] |
        [[T1 [T2 E0]] | [T1 [T2 E0]]]]]]];
        try (subst; exfalso; apply N3; reflexivity);
        try (apply TR in T2; discriminate T2).
      * (* the broadcaster would take the abort, which it never does *)
        apply TR in T2. injection T2 as EC EV. subst.
        eapply bc_abort_in_not; eassumption.
      * (* the overlap component takes the abort and leaves the nextSince states *)
        apply TR in T2. injection T2 as EC EV. subst.
        ent_state_comp NS.
        eapply ovlp_abort_in_notNextSince; eassumption.
Qed.
(**Proof: Similar to msgAbort_not_nextSince*)

(* If a message with mode m was delivered exactly AN time units ago, and the
coverage of the message was insufficient with respect to said mode, and we have
been awaiting a transition to m for some t time units greater than AN, then one
of two things holds. Either a) A notification of the message and its coverage is
pending immediately i.e. with timestamp 0 or b) the entity in question is on the
notification abort path. *)
Theorem instant_insuff_abort (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t : Time) (i : nat) (p : reachableProtNet n) : 
  delivered ([-[baseMode m, basePosition l], l0, r-]) adaptNotif i n p -> ~sufficient m r ->
  nextSince m t i n p -> adaptNotif < t ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n \/
  notifAbortPathNet i n. 
  (*Induction on delivered. BaseType case fails because of AN not equal 0.*)
  intros H H0 H1 H2.
  (*Induction on delivered. BaseType case fails because of AN not equal 0.*)
  dependent induction H. false. apply (Rlt_irrefl adaptNotif).
  eapply Rle_lt_trans. rewrite <- x. apply Rle_refl. apply adaptNotif_positive.
  (*Discrete inductive case: Apply I.H. to previous state, yielding incomingNetNotif
  <r, m, l> 0 i n \/ notifAbortPath m r i n.*)
  dependent destruction H1. false. eapply Rlt_not_le. apply H4. simpl. timeNonneg.
  lets IHdisc : IHdelivered H0 H1 H3. reflexivity.
  (*Now we do a case analysis on this disjunction. First off we have
  incomingNetNotif <r, m, l> 0 i n. We can show then by (insuff_incomingNet_abort) that our
  goal holds in the next state.*)
  elim_intro IHdisc D1 D2.
  assert (nextModeNet m i n) as Q. eapply nextSince_next. apply H1.
  eapply insuff_incomingNotif_abort. apply p. apply Q.
  apply w. assumption. assumption.
  (*Then there's the case where notifAbortPath m r i n. In this case, we can show by
  (notifAbort_not_nextSince) that either notifAbortPath m r i n' or ~nextSineState m i n'.*)
  lets G : notifAbort_not_nextSince p D2 w. elim_intro G G1 G2.
  (*The former gives us our goal by the RHS.*)
  right. assumption.
  (*The latter gives us a contradiction by nextSinceState*)
  false.
  (*Delay case: Apply (delivered_incomingNetNotif) to previous state and get
  incomingNetNotif <r, m, l> (AN _ (AN - d)) i n = incomingNetNotif <r, m, l> d i n.*)
  assert (t0 < adaptNotif) as Q. rewrite <- x. simpl. Rplus_lt_tac. delPos.
  lets W : delivered_incomingNetNotif H Q.
  (*Then by (Basics::incomingNetNotif_del) we get incomingNetNotif <r, m, l> 0 i n',
  our left disjunct.*)
  left. lets E : incomingNetNotif_del p w W. invertClearAs2 E Z1 Z2.
  my_applys_eq Z2. apply timeEqR. simpl. rewrite <- x. simpl. ring. Qed.

(* begin helpers for insuff_incomingNotif_bad *)
(** Only the listener inputs on AN: no broadcast or overlap state does.*)
Local Lemma broadcast_AN_in_not p p' v :
  broadcastState p -> p -PA- chanAN ;? v -PA> p' -> False.
Proof. intros S T. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra. Qed.

Local Lemma overlap_AN_in_not p p' v :
  overlapState p -> p -PA- chanAN ;? v -PA> p' -> False.
Proof. intros S T. destruct (overlapState_shape _ S); prot_outProc_in_not_contra. Qed.

(** A listener that inputs on AN is listening.*)
Local Lemma listener_AN_in_listening p p' v :
  listenerState p -> p -PA- chanAN ;? v -PA> p' -> listeningState p.
Proof.
  intros S T.
  destruct (listenerState_shape _ S) as [B | m B | B | m B | B | m l B | m e B | m e B | B | B];
    try exact B; prot_outProc_in_not_contra.
Qed.

(** Listening takes a notification of a range r insufficient for its mode m into rangeBad m.*)
Local Lemma listening_AN_insuff_rangeBad p p' r m l :
  listeningState p -> ~ sufficient m r ->
  p -PA- chanAN ;? [baseDistance r, baseMode m, basePosition l] -PA> p' ->
  rangeBadState m p'.
Proof.
  intros LS NS T. destruct (ProcEquiv.bisim_step_disc _ _ _ _ LS T) as [q [TQ B]].
  unfold listening in TQ. invert_disc_prefixes. explicit_typed_input. clean_proc_hyp B.
  red. eapply ProcEquiv.bisim_trans; [exact B | ]. unfold_app_bisim.
  assert (EB : evalBoolExp (bSufficient (eBase (baseMode m)) (eBase (baseDistance r))) false).
  { assert (F : suffBool m r = false)
      by (unfold suffBool; destruct (suffDec m r); [contradiction | reflexivity]).
    rewrite <- F. apply bevalSufficient_dist; apply evalBase. }
  eapply ProcEquiv.bisim_trans; [apply (ProcEquiv.if_then_bisim_false _ _ _ EB) | ].
  unfold_app_bisim. apply ProcEquiv.bisim_refl.
Qed.

(** A notification with timestamp 0 stays incoming across a discrete step of a reachable
network, unless the step is its entity's listener, listening, taking it, which leaves the
rest of the entity's software, its position and its mode state as they were.*)
Local Lemma incomingNetNotif_zero_disc n n' a i v :
  reachableProtNet n -> n -NA- a -NA> n' -> incomingNetNotif v zeroTime i n ->
  incomingNetNotif v zeroTime i n' \/
  exists p1 p2 p3 p3' lp h h' k,
    [|p1 $||$ p2 $||$ p3, lp, h, k|] @ i .: n /\
    [|p1 $||$ p2 $||$ p3', lp, h', k|] @ i .: n' /\
    listeningState p3 /\ p3 -PA- chanAN ;? v -PA> p3'.
Proof.
  intros RN S IN. destruct IN as [p lp li lo ln k E INL].
  destruct (link_net_ent_disc_fwd _ _ _ _ _ S E) as [e' [E' [EQ | [b B]]]].
  - subst e'. left. econstructor; eassumption.
  - lets PS : reachableProtNet_triple RN E. inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    inversion B; subst;
      try (left; econstructor; [exact E' | exact INL]; fail);
      match goal with [Hi : {| li := _; lo := _; ln := _ |} -i- _ -i> _ |- _] =>
        inversion Hi; subst end;
      try (left; econstructor; [exact E' | exact INL]; fail).
    + (* the interface hands a notification to the software *)
      match goal with [H : ln -nl- _ !! -nl> _ |- _] => inversion H; subst end.
      simpl in INL.
      match goal with [H : _ -tl- _ !! -tl> _ |- _] =>
        destruct (timedList_out _ _ _ _ H INL) as [IN' | EQ] end.
      * left. econstructor; [exact E' | exact IN'].
      * injection EQ as EV. subst. right.
        match goal with [H : _ $||$ _ $||$ _ -PA- chanAN ;? _ -PA> _ |- _] =>
          triple_disc_nonTau H end.
        -- exfalso. eapply broadcast_AN_in_not; eassumption.
        -- exfalso. eapply overlap_AN_in_not; eassumption.
        -- do 8 eexists. split; [exact E | ]. split; [exact E' | ]. split; [ | eassumption].
           eapply listener_AN_in_listening; eassumption.
    + (* the interface broadcasts and buffers a new notification *)
      left. econstructor; [exact E' | ]. eapply notifList_in_pres; eassumption.
Qed.
(* end helpers *)

Theorem insuff_incomingNotif_bad (n n' : Network) (a : ActDiscNet) (m : Mode)
  (r : Distance) (l : Position) (i : nat) : 
  reachableProtNet n -> currModeNet m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
  notifBadPathNet i n'.
Proof.
  intros RN CM S NS IN.
  destruct (incomingNetNotif_zero_disc _ _ _ _ _ RN S IN)
    as [IN' | [p1 [p2 [p3 [p3' [lp [h [h' [k [E [E' [LS T]]]]]]]]]]]].
  - left. exact IN'.
  - (* the listener took the notification into rangeBad m, and the mode is still m *)
    right. econstructor; [ | exact E']. eapply nbpRng.
    + constructor. eapply listening_AN_insuff_rangeBad; eassumption.
    + lets C : liftEntNet_ent CM E. simpl in C. exact C.
Qed.
(*Proof: Much like insuff_incomingNotif_abort.*)

(** If the badOvlp state holds at a particular reachable state,
and in the next state listening holds, then the next state is tfs for some
time t, with the mode parameter equal to the current mode.*)
(* begin helpers for badOvlp_listening_tfs *)
Ltac badOvlp_listening_tfs_close :=
  unfold bcWaitState, sleepingState, bcReadyState, dormantState, ovWaitState,
    ovReadyState, switchBcState, switchCurrState, switchListenState, tfsStartState,
    tfsNextState, tfsCurrState, tfsBcState, tfsListenState, initState, ovAbortState,
    listeningState, rangeBadState, currOKState, abortOvlpState, badOvlpState,
    currCompState, pausedState, gotMsgState, gotRangeState, currEqState, nextEqState,
    currPincCheckState, nextPincCheckState in *;
  match goal with
  | [V : ProcEquiv.bisimulation ?p ?x, V1 : ProcEquiv.bisimulation ?p ?y |- False] =>
    let BT := fresh "BT" in
    assert (ProcEquiv.bisimulation x y) as BT by
      (eapply ProcEquiv.bisim_trans; [apply ProcEquiv.bisim_symm; exact V | exact V1]);
    unfold bcWait, sleeping, bcReady, dormant, init, ovWait, ovReady, switchBc,
      switchCurr, switchListen, tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen, ovAbort,
      listening, checkRange, rangeBad, currEq, badOvlp, currOK, nextEq, abortOvlp,
      gotMsg, gotRange, currPincCheck, currComp, nextPincCheck, paused in BT;
    first [solve [bisim_contra BT] |
      apply ProcEquiv.bisim_symm in BT; solve [bisim_contra BT]]
  end.
(* end helpers *)

Theorem badOvlp_listening_tfs n n' a i m 
  (rn : reachableProtNet n) (w : n -NA- a -NA> n') :
  badOvlpStateNet i n -> listeningStateNet i n' ->
  currModeNet m i n ->
  exists t, tfs m t i n' (reachNetDisc n n' a rn w).
Proof.
  intros BO LS CM.
  assert (msgBadPathNet i n) as MB.
  { destruct BO as [e E I]. econstructor; [ | exact I].
    inversion E as [q l h k P]; subst. apply mbpBad. exact P. }
  destruct (msgBad_disc_net n n' a i m rn w MB CM) as [MB' | TF].
  - exfalso. destruct MB' as [e E I]. destruct LS as [e' E' I'].
    pose proof (entInNetUnique _ _ _ _ I I') as EQ. subst e'.
    inversion E' as [q l h k LP]; subst.
    inversion LP as [p1 p2 p3 L3]; subst.
    inversion E; subst;
    match goal with
    | H : gotMsgStateProt _ _ _ |- _ => inversion H; subst
    | H : gotRangeStateProt _ _ _ |- _ => inversion H; subst
    | H : badOvlpStateProt _ |- _ => inversion H; subst
    end; badOvlp_listening_tfs_close.
  - exists zeroTime. exact TF.
Qed.

(*If an entity is on the notification bad path, and a discrete transition
happens, then in the next state it is either still on the notification bad path,
or the tfs relation holds in the next state.*)
Theorem notifBad_pres_tfs (m : Mode) (n n' : Network)
  (a : ActDiscNet) (i : nat) (rn : reachableProtNet n)
  (w : n -NA- a -NA> n') : 
  notifBadPathNet i n -> currModeNet m i n' -> ~failSafe m ->
  notifBadPathNet i n' \/ (exists t, tfs m t i n' (reachNetDisc n n' a rn w)).
  introz U.
  (*Case analyse the notifBadPath using notifBadPathNet_cases.*)
  lets CPB : currModeNet_notifBad_pres_bkwd U0 U U1.
  elim_intro CPB CMN TFD.
  lets NBC : notifBadPathNet_cases U CMN. or_flat. ex_flat.
  (*In the rangeBad case, forward tracking gives you a state that will
  yield notifBadPathNet.*)
  lets RNN : rangeBad_next_net rn w OR CMN. left. or_flat.
  eapply rangeBad_notifBad_net; eassumption.
  ex_flat.
  assert (badOvlpStateNet i n') as BOS. eapply currEq_eq_badOvlp_net.
  reflexivity. eassumption. apply badOvlp_notifBad_net; assumption.
  (*In the badOvlp case, fwd-tracking gives one case of badOvlp,
  which also yields notifBadPath.*)
  lets BNN : badOvlp_next_net w OR0. or_flat.
  left. apply badOvlp_notifBad_net; assumption.
  (*So now we are left with the case of the transition from badovlp to listening.
  From here, we simply apply an auxiliary result saying that tfs is implies, and
  the proof is complete.*)
  right. eapply badOvlp_listening_tfs; eassumption.
  (*We finally deal with the remaining tfs case generated by a previous
  application of currModeNet_notifBad_pres_bkwd.*)
  right. apply TFD. Qed.

Lemma tfs_pres_not_currSince m t i n n' p a
  (w : n -NA- a -NA> n') : tfs m t i n p ->
  tfs m t i n' (reachNetDisc n n' a p w) \/
  (forall m' t' p', ~ failSafe m' -> ~currSince m' t' i n p').
Proof.
  intro U.
  lets D : tfsStateNet_dec i n'. unfold decidable in D.
  destruct D as [D | D].
  - left. apply tfsDisc; assumption.
  - right. intros m' t' p' NFS.
    eapply (tfsState_not_currSince m' t' i n n' p' a w NFS).
    + eapply tfs_rel_state. eassumption.
    + assumption.
Qed.

(* If a message with mode m was delivered exactly AN time units ago, and the coverage
of the message was insufficient with respect to said mode, and we have been broadcasting
in mode m for some t time units greater than AN, then one of 3 things holds. 
Either a) A notification of the message and its coverage is pending immediately i.e. 
with timestamp 0 or b) the entity in question is on the notification bad path or 
c) we are at the beginning of a transition to a fail safe mode. *)
Theorem instant_insuff_bad (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t : Time) (i : nat) (p : reachableProtNet n) : 
  delivered ([-[baseMode m, basePosition l], l0, r-]) adaptNotif i n p -> ~failSafe m ->
  ~sufficient m r -> currSince m t i n p -> adaptNotif < t ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n
  \/ notifBadPathNet i n \/ exists t, tfs m t i n p.
  intros H NFS H0 H1 H2. lets CSS : H1.
  (*Induction on delivered. BaseType case fails by contradiction on AN = 0.*)
  dependent induction H. false. apply (Rlt_irrefl adaptNotif).
  eapply Rle_lt_trans. rewrite <- x. apply Rle_refl. apply adaptNotif_positive.
  (*Discrete Inductive case. Destruct currSince for previous cases.*)
  dependent destruction H1.
  (*Get rid of the case where the previous state was nextSince
  first apply instant_insuff_abort. Then show that the transition from nextSince to
  currSince was impossible for notifAbortPathNet and so message must be incoming. Then
  show that the transition from nextSince to currSince preserves incoming, giving us LHS*)
  lets IIA : instant_insuff_abort H H0 H1 H4.
  (*To use later: let's show that we're in a switch state and hence are paused.*)
  assert (reachableProtNet n') as p'. eapply reachNetDisc; eassumption.
  assert (switchStateNet i n') as SSN2. inversion H3. inversion H5. inversion H7.
  netState_auto_pre. eapply switLisSt. eassumption.
  assert (switchStateNet i n) as SSN1. inversion H2. inversion H5. inversion H7.
  netState_auto_pre. eapply switCurSt. eassumption.
  lets PSN2 : paused_switch_net i p'. rewrite <- PSN2 in SSN2.
  lets PSN1 : paused_switch_net i p. rewrite <- PSN1 in SSN1.  
  (*OK, now we're back to the run of the mill, a few contradictions to come later.*)
  rename H2 into SWIN. elim IIA; [intro IL | intro IR]; clear IIA.
  assert (nextModeNet m i n) as NM. eapply nextSince_next. eassumption.
  lets IIA : insuff_incomingNotif_abort p NM w H0 IL. elim_intro IIA IIL IIR.
  left. assumption.
  (*OK, so contradictions follow from the assertion of paused contradicting with the
  notifAbortPath, either now or in the previous state.*)
  false. eapply state_disj_paused_notifAbort. apply SSN2. assumption.
  false. eapply state_disj_paused_notifAbort. apply SSN1. assumption.
  (*OK, now we're at a case where the previous state is currSince,
  so we can apply I.H. to previous state, yielding
  incomingNetNotif <r, m, l> 0 i n \/ notifAbortPath m r i n \/ tfs 0.*)
  lets IH : IHdelivered NFS H0 H1 H3. reflexivity.
  (*We then break the IH into its three cases and prove each separately.*)
  lets IHC : IH H1. clear IH. rename IHC into IH. elimOr3 IH IH.
  (*First, there's the semi-preservation of incomingNetNotif,zeroTime by a discrete
  transition and currSince (and so currMode) holding. So first we assert that currMode
  holds and then we can apply this theorem.*)
  assert (currModeNet m i n) as CMN. eapply currSince_curr. eassumption.
  lets IIB : insuff_incomingNotif_bad p CMN w H0 IH0.
  elim_intro IIB INN NBN. left. assumption. right. left. assumption.
  (*Then notifBadPathNet is shown to be either preserved or goes to tfs*)
  right. eapply notifBad_pres_tfs; assumption.
  (*Now tfs is shown to hold in the previous state, and we must show it to hold now.
  Well, a separate result gives us two cases to consider. First, tfs holds in the next
  state. In this case, we're done. Else, ~currSince must hold in the next state-
  which contradicts a hypothesis. So we're done in any case.*)
  invertClearAs2 IH t0 TFS.
  lets TPNC : tfs_pres_not_currSince w TFS. elim_intro TPNC TF NCS.
  right. right. exists t0. assumption. false. eapply NCS; eassumption.
  (*Delay inductive case: previous state must have delivered the message at some t' < AN.
  Then from (delivered_incomingNetNotif) and incomingNetNotif delay constructor,
  we have the LHS.*)
  assert (t0 < adaptNotif) as TLAN. rewrite <- x. simpl. Rplus_lt_tac.
  delPos. lets DIN : delivered_incomingNetNotif H TLAN. left. 
  lets IND : incomingNetNotif_del p w DIN. destruct IND. my_applys_eq i0.
  apply timeEqR. simpl. rewrite <- x. simpl. ring.
  (*Note, the proof is Similar to instant_insuff_abort.*)
  Qed.

(* If a message was delivered t' time units ago, and we have been waiting to
enter the next mode m for some time t, with t' < t, and the time since delivery
is greater than AN, then message delivery in question was sufficient.*)
Theorem deliv_next_suff (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t t' : Time) (i : nat) (p : reachableProtNet n) :
  nextSince m t i n p ->
  delivered ([-[baseMode m, basePosition l], l0, r-]) t' i n p ->
  adaptNotif < t' -> t' < t -> sufficient m r.
  introv H H0. gen t.
  (*Induction on delivered.*)
  induction H0; intros u G1 G2 G3; [false | dependent destruction G1..].
  (*The base case fails because of AN < 0.*)
  false. eapply Rlt_not_le. apply G2. simpl. timeNonneg.
  (*For the inductive cases, we can know that since delivered and nextSince share
  the same history p, that the previous state was also nextSince- we show this
  via an inversion on nextSince. One of these cases is contradictory with t0 < t.*)
  false. eapply Rlt_not_le. apply G3. simpl. timeNonneg.
  (*In the discrete inductive case we notice that t & t' haven't changed and so we just
  apply the I.H.*)
  eapply IHdelivered; try assumption. apply G1. apply G3.
  (*In the timed case, we do a case analysis on AN < t in the previous case.*)
  lets Q : Rlt_or_le adaptNotif t.
  elim_intro Q Q1 Q2.
  (*On the one hand, we may have AN < t, in which case we can just apply the I.H.*)
  eapply IHdelivered; try assumption. apply G1. simpl in G3. Rplus_lt_tac.
  (*Which leaves us with the other case, t <= AN, the only part of the proof that requires real thinking.
  Well, we again do a case analysis this time on t < AN or t = AN.*)
  apply Rle_lt_or_eq_dec in Q2. elim_intro Q2 F1 F2.
  (*If t' < AN, then by (delivered_incomingNetNotif), we get incomingNetNotif <r, m, l0> (AN - t') i n.*)
  lets K : delivered_incomingNetNotif H0 F1.
  (*Now, we already have from our hypothesis that AN < t' + d, rearranging to AN - t' < d.
  However, (Basiscs::incomingNetNotif-del) gives us that d <= AN - t', which is a
  contradiction.*)
  lets K1 : incomingNetNotif_del p w K. invertClearAs2 K1 K2 K3. simpl in K2. false.
  eapply Rle_not_lt. apply K2. simpl in G2. Rplus_lt_tac.
  (*So we are left with the case where t' = AN. We proceed from here by reductio
  ad absurdum, that is assume ~sufficient m r towards a contradiction.*)
  lets K : suffDec m r. elim_intro K K1 K2. assumption.
  (*We have enough information to apply (instant_insuff_abort) giving us
  incomingNetNotif <m, l, r> 0 i n \/ notifAbortPath m r i n.*)
  replace t with adaptNotif in H0; [ |apply timeEqR; symmetry; assumption].
  assert (adaptNotif < t0) as H. simpl in G3. rewrite F2 in G3. Rplus_lt_tac.
  lets G : instant_insuff_abort H0 K2 G1 H.
  (*We case analyse this disjunction.*)
  elim_intro G H1 H2.
  (*The first case fails by contradiction via an application of (Basiscs::incomingNetNotif_del)
  yielding d <= 0, impossible for a strictly positive delay.*)
  lets H4 : incomingNetNotif_del p w H1. invertClearAs2 H4 H5 H6. false.
  eapply Rle_not_lt. apply H5. simpl. delPos.
  (*The next case fails also because it can be shown that delay is impossible whenever we're on a
  notifAbortPath m r i n (...EA::notifAbortPath_urgent...). Hence we arrive at
  contradiction and conclude that the coverage is sufficient.*)
  lets nau : notifAbortPathNet_urgent p H2 w. contradiction nau.
  (*Note, this theorem bears resemblance to incomp_bad in how it is proved.*)
  Qed.

(* If an insufficient message was delivered t' time units ago, wtih AN < t',
and we've been currSince for some time t greater than t', then we are tfs for
some x > (t' - AN) time units.*)
Theorem insuff_react (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t t' : Time) (i : nat) (p : reachableProtNet n) :
  currSince m t i n p -> 
  delivered ([-[baseMode m, basePosition l], l0, r-]) t' i n p ->
  forall q : adaptNotif < t', t' < t ->  ~sufficient m r -> ~failSafe m ->
  exists x, minusTime t' adaptNotif (Rlt_le adaptNotif t' q) <= (time x) /\
  tfs m x i n p.
  (*Induction on currSince.*)
  intro. generalize dependent l. generalize dependent l0. generalize dependent r.
  generalize dependent t'. induction H; intros;
  match goal with [ H : ~failSafe m |- _ ] => rename H into Q end.
  (*In the base case, we proceed via contradiction. We get that the previous state was
  nextSince. We note that no time has passed since the previous state. Also, the action
  linking the the previous state to the current one is a tau, we show this.*)
  addHyp (switchCurr_listen_trans_tau n n' a i w H0 H1).
  (*So then delivered must be true for the previous state also, because the base case
  doesn't match against a tau.*)
  generalize dependent w. rewrite H5. intros. dependent destruction H2.
  (*But then by (deliv_next_suff), we can show sufficient m r*)
  addHyp (deliv_next_suff n m l l0 r t t0 i p H H2 q H3).
  (*This in direct contradiction with one of our hypothesis.*)
  contradiction H4.
  (*In the discrete inductive case, we can apply the I.H.*) 
  dependent destruction H1. contradict q. eapply Rle_not_lt.
  simpl. timeNonneg.
  addHyp (IHcurrSince t0 r l0 l H1 q H2 H3 Q). clear IHcurrSince.
  (*Tidy up the existential*)
  invertClearAs2 H4 x TFA. decompAnd2 TFA TFL TF. rename TF into H4.
  (*Then we must establish that we are currently still in a tfs state.*)
  assert (tfsStateNet i n'). apply currSince_curr in H.
  apply tfs_rel_state in H4. apply (tfs_currMode_disc_pres n n' a i m p w H Q H4).
  (*Then the discrete consructor for tfs does the rest and the case is done.*)
  exists x. split. assumption. constructor; assumption.
  (*In the delay inductive case, we first assert t' < t from t' + d < t + d*)
  dependent destruction H0. rename t0 into t'.
  assert (t' < t). eapply Rplus_lt_reg_r. unfold addDelayTime in H1.
  simpl in H1.  apply H1.
  (*Then we split this further depending on whether AN < t'*)
  addHyp (Rlt_or_le adaptNotif t'). invertClear H4.
  (*Make the IH a bit more useable.*)
  lets IH : IHcurrSince H0 H5 H3 H2 Q. decompExAnd IH x TL TF. clear IHcurrSince.
  (*First, let's assume it is. Then we can apply the I.H. and the delay constructor
  of tfs and we're done.*)
  replace ((minusTime (nonneg (time (delToTime (t' +dt+ d))))
  (nonneg (time adaptNotif)) (Rlt_le (nonneg (time adaptNotif))
  (nonneg (time (delToTime (t' +dt+ d)))) q))) with
  (delToTime (minusTime t' adaptNotif (Rlt_le adaptNotif t' H5) +dt+ d)).
  exists (x +dt+ d). split. apply Rplus_le_compat_r. assumption.
  constructor. assumption. apply timeEqR. simpl. ring.
  (*Otherwise, t' <= AN. In which case we have either t' < AN or t' = AN.*)
  remember ([baseMode m, basePosition l]) as v. apply Rle_lt_or_eq_dec in H5. invertClear H5.
  (*We apply (delivered_incomingNetNotif) for the t' < AN case, towards a contradiction.*)
  addHyp (delivered_incomingNetNotif n v r l0 t' i p H0 H4).
  remember (minusTime (nonneg (time adaptNotif)) (nonneg (time t'))
  (Rlt_le (nonneg (time t')) (nonneg (time adaptNotif)) H4)) as t''.
  rewrite Heqv in H5.
  addHyp (incomingNetNotif_del n n' d r m l t'' i p w H5). invertClear H6.
  rename x into Q1. generalize dependent Q1. rewrite Heqt''. intros.
  simpl in Q1. simpl in q.
  (*The contradiction comes in the form d <= AN - t' < d*)
  assert (adaptNotif - t' < d). apply Rplus_lt_swap_rl. assumption.
  contradict H6. apply Rle_not_lt. assumption.
  (*So now we have the t' = AN case and we apply (instant_insuff_bad)*)
  apply timeEqR in H4. rewrite H4 in H0, H3. rewrite Heqv in H0.
  addHyp (instant_insuff_bad n m l l0 r t i p H0 Q H2 H H3).
  (*This leaves us with 3 sub cases on which to discriminate.*)
  decompose [or] H5; clear H5.
  (*The first two cases fail because delay can be shown to be impossible (...urgency...).*)
  addHyp (incomingNetNotif_del n n' d r m l zeroTime i p w H6). invertClear H5.
  rename x into Q2. clear H7. contradict Q2. apply Rlt_not_le. simpl. delPos.
  contradiction (notifBadPathNet_urgent i n n' d p H7 w).
  (*Hence we are left with t' = AN and tfs m t i n for some t. In this case, we apply the tfs
  delay constructor to show tfs m (t + d) i n which is exactly our goal simplified from
  tfs m (AN + t + d - AN) i n p.*)
  invertClearAs2 H7 x TF. lets TFD : tfsDel w TF. exists (x +dt+ d).
  split. simpl. rewrite H4. apply Rminus_le_swap_lr. cut (0 <= x). intro LT0.
  my_applys_eq LT0. ring. timeNonneg. apply TFD. Qed.
  (*
  >The following picture captures the intuition of this proof:

  currSince --------------t----------------------------
      insuff-deliv--------t'---------------------------
                  ------AN------------
                                      -------tfs-------
  *)

