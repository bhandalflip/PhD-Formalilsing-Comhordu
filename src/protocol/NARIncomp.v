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
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults.
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.NARMisc.
Require Import ComhCoq.protocol.ProtocolBridge.

Section NARIncomp.
Context {Model : ComhModel}.

(*If any entity has an incomingNet message of a mode and a position, the network can't
delay.*)
Theorem incomingNet_urgent (n n' : Network) (m : Mode) (l : Position) (i : nat) (d : Delay) :
  reachableProtNet n -> incomingNet [baseMode m, basePosition l] i n -> ~n -ND- d -ND> n'.
Proof.
  intros RN IN DEL. destruct IN as [p l0 li lo ln k E IL].
  lets LS : del_listening_net RN DEL E. lets LE : liftEntNet_ent LS E.
  inversion LE as [p' l1 h1 k1 LP]; subst.
  inversion LP as [p1 p2 p3 L3]; subst.
  destruct (del_net_ent _ _ _ _ _ E DEL) as [e' ED].
  eapply (ent_del_sync_inter_not _ _ _ _ _ _ (chanInProc ;? [baseMode m, basePosition l]));
    [ | | exact ED].
  - dae_listener. eapply bisim_dae; [apply bisim_symm; exact L3 | ]. unfold listening.
    apply daeSumL; apply daeSumL; apply daeSumR. apply dae_inPfx. typed_vals.
  - destruct li as [tl]. simpl in IL.
    destruct (timedList_timeout_enabled _ _ IL) as [tl' T].
    eapply daeiOut. apply stepIntFwdIn. apply stepIlLift. exact T.
Qed.
(**Proof: First we show by inversion on incomingNet v i n that there is some e @ i .: n.
Now assume there was such a del towards a contradiction. Then by (del_listening) we'd have
listeningState i n. But then it can be shown by (...listening-inProc...) that the software
component is capable of consuming any pending message. So a tau can happen by synchronidastion
with the incomingNet message- this may be a separate result. So by [maximal progress- salvaged?
a delay is not possible, contradicting the earlier assumtion.*)

(** Across a step of a reachable network, a pending message of a mode and a position is
still pending, or the listener has just taken it into gotMsg, at the same position and with
the same mode state.*)
Local Lemma incomingNet_consume (n n' : Network) (a : ActDiscNet) (m : Mode) (l : Position)
  (i : nat) : reachableProtNet n -> n -NA- a -NA> n' ->
  incomingNet [baseMode m, basePosition l] i n ->
  incomingNet [baseMode m, basePosition l] i n' \/
  exists p p' l0 h h' k, [|p, l0, h, k|] @ i .: n /\ [|p', l0, h', k|] @ i .: n' /\
    gotMsgStateProt m l p'.
Proof.
  intros RN S IN. destruct IN as [p l0 li lo ln k E IL].
  destruct (link_net_ent_disc_fwd _ _ _ _ _ S E) as [e' [E' [EQ | [b B]]]].
  - subst e'. left. econstructor; [exact E' | exact IL].
  - destruct e' as [p' l' h' k']. destruct h' as [li' lo' ln'].
    destruct (link_ent_inter_disc _ _ _ _ _ _ _ _ _ B) as [EH | [EK EX]].
    + injection EH as EL1 EL2 EL3. subst. left. econstructor; [exact E' | exact IL].
    + subst k'.
      assert (PRES : forall c, (mkInterface li lo ln -i- c -i> mkInterface li' lo' ln') ->
        (forall d : Delay, c <> d) ->
        <( [baseMode m, basePosition l], zeroTime )> _: inList li' \/
        c = chanInProc {! [baseMode m, basePosition l]).
      { intros c T NDc. eapply inList_inter_pres_input; [exact NDc | exact IL | exact T]. }
      destruct EX as [[v [T P]] | [[v [T P]] | [[v [T P]] | [[v T] | [v [r T]]]]]];
        (destruct (PRES _ T ltac:(intros dd DD; discriminate DD)) as [IL' | CE];
         [left; econstructor; [exact E' | exact IL'] | ]); try discriminate CE.
      injection CE as CE. subst v.
      assert (l' = l0) by (symmetry; apply (stepEnt_disc_pres_pos _ _ _ B)). subst l'.
      right. exists p p' l0 (mkInterface li lo ln) (mkInterface li' lo' ln') k.
      split; [exact E | ]. split; [exact E' | ].
      eapply gotMsg_state; [ | exact P].
      eapply reachableProtNet_triple; [exact RN | exact E].
Qed.

(*If an incoming message is incompatible with the current mode & the position,
then in the next state, it is either still incoming or we have entered the msgBadPath.*)
Theorem incomp_incomingNet_bad (n n' : Network) (a : ActDiscNet) (l l' : Position) (i : nat)
  (m m' : Mode) :
  reachableProtNet n -> n -NA- a -NA> n' -> inPosNet l i n -> currModeNet m i n ->
  incomingNet [baseMode m', basePosition l'] i n ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n' \/
  msgBadPathNet i n'.
Proof.
  intros RN S IP CM IN PI.
  destruct (incomingNet_consume _ _ _ _ _ _ RN S IN)
    as [IN' | [q [q' [l0 [h [h' [k [E [E' G]]]]]]]]]; [left; exact IN' | right].
  assert (l0 = l) by (eapply inPos_unique; [econstructor; exact E | exact IP]). subst l0.
  lets CMk : liftEntNet_ent CM E. simpl in CMk.
  econstructor; [ | exact E']. eapply mbpMsg; [exact G | exact CMk | exact PI].
Qed.
  (*If the action a is not an input of [m, l], then [m, l] must
  still be contained in the input list. Then show that if a is such an input, the
  base case for msgBadPathNet is satisfied.*)

(**If an incomingNet message is incompatible with the
next mode & the position, then in the next state, it is either still incomingNet
or we have entered the msgAbortPath, or the msgBadPath if it is incompatible with the
current mode too.*)
Theorem incomp_incomingNet_abort (n n' : Network) (a : ActDiscNet) (l l' : Position) (i : nat)
  (m m' : Mode) : reachableProtNet n -> n -NA- a -NA> n' -> inPosNet l i n ->
  nextModeNet m i n ->
  incomingNet [baseMode m', basePosition l'] i n ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n' \/ msgAbortPathNet i n' \/
  msgBadPathNet i n'.
Proof.
  intros RN S IP NM IN PI.
  destruct (incomingNet_consume _ _ _ _ _ _ RN S IN)
    as [IN' | [q [q' [l0 [h [h' [k [E [E' G]]]]]]]]]; [left; exact IN' | right].
  assert (l0 = l) by (eapply inPos_unique; [econstructor; exact E | exact IP]). subst l0.
  lets NMk : liftEntNet_ent NM E. simpl in NMk.
  destruct (possIncDec (currModeMState k) m'
    (mkDistance (dist2d l l' -nn- speedMax *nn* msgLatency))) as [P | NP].
  - right. econstructor; [ | exact E']. eapply mbpMsg; [exact G | reflexivity | exact P].
  - left. econstructor; [ | exact E'].
    eapply mapMsg; [exact G | reflexivity | exact NP | exact NMk | exact PI].
Qed.

(**Proof: Analogous to incomp_incomingNet_bad.*)

Theorem msgAbort_not_nextSince (n n' : Network) (a : ActDiscNet)
  (i : nat) (rn : reachableProtNet n) :
  msgAbortPathNet i n -> n -NA- a -NA> n' -> 
  msgAbortPathNet i n' \/ ~nextSinceStateNet i n'.
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
  pose proof (stepEnt_disc_pres_pos _ _ _ ST) as LE. simpl in LE. subst l'.
  destruct (eqDecProcTerm p3 p3') as [E3 | N3].
  - (* the listener stays: the path holds again unless the mode state changed, which only
       the overlap component's switch or abort does *)
    subst p3'.
    assert (KS : forall m', nextModeMState k = Some m' -> k = k' \/
      ~ nextSinceStateEnt ([|p1' $||$ p2' $||$ p3, l, h', k'|])).
    { intros m' NM. destruct (eqDecModeState k k') as [KE | KN]; [left; exact KE | right].
      eapply mState_change_not_nextSince_ent; [exact R | | exact KN | exact ST].
      eapply nextMode_unstable. exact NM. }
    inversion E; subst.
    + match goal with [H : gotMsgStateProt _ _ _ |- _] => inversion H as [? ? ? G]; subst end.
      match goal with [NM : nextModeMState k = Some ?m' |- _] =>
        destruct (KS m' NM) as [KE | NS]; [subst k'; left | right; apply NSN; exact NS] end.
      econstructor; [ | exact I'].
      eapply mapMsg; [constructor; exact G | reflexivity | eassumption | eassumption | eassumption].
    + match goal with [H : gotRangeStateProt _ _ _ |- _] => inversion H as [? ? ? G]; subst end.
      match goal with [NM : nextModeMState k = Some ?m' |- _] =>
        destruct (KS m' NM) as [KE | NS]; [subst k'; left | right; apply NSN; exact NS] end.
      econstructor; [ | exact I'].
      eapply mapGrng; [constructor; exact G | reflexivity | eassumption | eassumption | eassumption].
    + match goal with [H : currCompStateProt _ _ _ |- _] => inversion H as [? ? ? G]; subst end.
      match goal with [NM : nextModeMState k = Some ?m' |- _] =>
        destruct (KS m' NM) as [KE | NS]; [subst k'; left | right; apply NSN; exact NS] end.
      econstructor; [ | exact I'].
      eapply mapCuco; [constructor; exact G | eassumption | eassumption].
    + match goal with [H : abortOvlpStateProt _ |- _] => inversion H as [? ? ? AO]; subst end.
      left. econstructor; [ | exact I']. eapply mapAbort. constructor. exact AO.
  - (* the listener steps *)
    destruct W3 as [E3 | [b3 T3]]; [contradiction | ].
    inversion E; subst.
    + (* gotMsg: it reads the entity's position, into gotRange with the range computed from
         it, the range the path tests *)
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
      eapply mapGrng; [constructor; exact GR | reflexivity | eassumption | eassumption
        | eassumption].
    + (* gotRange: it reads the current mode, not possibly incompatible, into currComp *)
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
      eapply mapCuco; [ | eassumption | eassumption].
      constructor. eapply currPincCheck_cond_false; [eassumption | exact CP].
    + (* currComp: with a next mode, it reads it on mNext, into abortOvlp *)
      match goal with [H : currCompStateProt _ _ _ |- _] => inversion H as [? ? ? G]; subst end.
      assert (ACT : forall c, p3 -PA- c -PA> p3' -> entChanAct c).
      { intros c T. destruct (currComp_next_act _ _ _ _ _ T G) as [[EC _] | [v [EC _]]];
          subst c; left; reflexivity. }
      destruct (triple_disc_ent_chan 2 R ST eq_refl eq_refl ACT) as [E3 | ST3];
        [contradiction | ].
      destruct (ent_disc_proc_read _ _ _ _ _ _ _ _ _ ST3)
        as [E3 | [c [T [_ [_ [RN RS]]]]]]; [contradiction | ].
      destruct (currComp_next_act _ _ _ _ _ T G) as [[EC _] | [v [EC NP]]].
      * destruct (RS EC) as [NN _]. congruence.
      * destruct (RN v EC) as [NM KE]. subst k'.
        left. econstructor; [ | exact I']. eapply mapAbort. constructor.
        eapply nextPincCheck_cond_true; [ | exact NP].
        match goal with [NM' : nextModeMState k = Some ?m', P : possiblyIncompatible ?m' _ _ |- _] =>
          rewrite NM in NM'; injection NM' as NM'; subst; exact P end.
    + (* abortOvlp: it outputs on abort, which only the overlap component can take, and
         the overlap component then leaves the nextSince states *)
      match goal with [H : abortOvlpStateProt _ |- _] =>
        inversion H as [? ? ? AO]; subst end.
      assert (TR : forall c, p3 -PA- c -PA> p3' -> c = chanAbort ;! []).
      { intros c T. eapply abortOvlp_listening_track; [exact AO | | exact T].
        eapply abortOvlp_next; eassumption. }
      right. apply NSN. intro NS.
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
      * apply TR in T2. injection T2 as EC EV. subst.
        eapply bc_abort_in_not; eassumption.
      * apply TR in T2. injection T2 as EC EV. subst.
        ent_state_comp NS.
        eapply ovlp_abort_in_notNextSince; eassumption.
Qed.

(** No entity of a network is both in a tfs state and in a nextSince state.*)
Local Lemma tfsStateNet_nextSinceStateNet_disj i n :
  tfsStateNet i n -> nextSinceStateNet i n -> False.
Proof.
  intros [e TE E] [e' NE E']. pose proof (entInNetUnique _ _ _ _ E E') as EQ. subst e'.
  inversion TE as [q l0 h0 k0 TP]; subst. inversion TP as [q1 q2 q3 T]; subst.
  inversion NE as [q l1 h1 k1 NP]; subst. inversion NP as [r1 r2 r3 N]; subst.
  destruct T as [A | m A | A | A | A];
    destruct N as [m1 t1 x1 y1 B | m1 t1 l2 B | m1 B | m1 B];
    unfold tfsStartState, tfsNextState, tfsCurrState, tfsBcState, tfsListenState,
      ovWaitState, ovReadyState, switchBcState, switchCurrState in *; ov_disj A B.
Qed.

(* This says that if a message was just received this instant
and it's possibly incompatible with the  pending mode and position,
then either a) it is pending consumption or b) the message in question
is being processed along the "msgAbortPath" or c) along the "msgBadPath", when it is
possibly incompatible with the current mode too.*)
Theorem instant_incomp_abort (n : Network) (t : Time) (l l' : Position) (i : nat)
  (m m' : Mode) (p : reachableProtNet n) :
  nextSince m t i n p -> inPosNet l i n -> 0 < t ->
  received [baseMode m', basePosition l'] zeroTime i n p ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n  \/
  msgAbortPathNet i n \/ msgBadPathNet i n.
Proof.
  intros U U0 LT U1 U2.
  (*Induction on received.*)
  dependent induction U1.
  (*In the base case of received it is easy to show that the message is in the
  input list and hence incoming.*)  
  left. eapply incoming_ent_net. eapply input_incomingEnt.
  apply H1. assumption.
  (*Discrete inductive case: first clear up some mess that doesn't fit*)
  dependent destruction U. false. eapply Rlt_not_le. apply LT. simpl. apply Rle_refl.
  (*Then let's assert that position hasn't changed.*)
  assert (inPosNet l i n) as IP. inposdp.
  (*Triviality for a hypothesis.*)
  assert ({| time := zeroNonneg |} = zeroTime) as TZ. reflexivity.
  (*Apply I.H. to previous state, yielding incomingNetNotif <r, m, l> 0 i n \/
  msgAbortPath m r i n \/ msgBadPath m r i n.*)
  lets IHdisc : IHU1 U IP TZ U2. clear IHU1.
  (*Now we do a case analysis on this disjunction.*)
  destruct IHdisc as [IN | [MA | MB]].
  (*First off we have incomingNet <r, m, l> 0 i n. We can show then by
  (incomp_incomingNet_abort) that our goal holds in the next state.*)
  assert (nextModeNet m i n) as NM. eapply nextSince_next. apply U.
  lets II : (>> incomp_incomingNet_abort p w IP NM IN U2). apply II.
  (*Then there's the case where msgAbortPath m r i n. In this case, we can show by
  (msgAbort_not_nextSince) that either msgAbortPath m r i n' or ~nextSineState m i n'.*)
  lets MN : msgAbort_not_nextSince p MA w. elim_intro MN MP NS.
  (*The former gives us our goal by the RHS.*)
  right. left. assumption.
  (*The latter gives us a contradiction by nextSinceState*)
  false.
  (*Then there's the case where msgBadPath m r i n. By (msgBad_disc_net), either
  msgBadPath m r i n' or the entity is in a tfs state, which is no nextSince state.*)
  assert (exists m0, currModeNet m0 i n) as CMX. destruct MB as [e _ E].
  exists (currModeEnt e). econstructor; [reflexivity | exact E]. destruct CMX as [m0 CM].
  lets MD : msgBad_disc_net p w MB. elim_intro MD MB' TS.
  right. right. assumption.
  false. eapply tfsStateNet_nextSinceStateNet_disj; eassumption.
  (*Delay case: contradicion, the time parameter to received was assumed to be 0*)
  false. eapply Rle_not_lt. apply Req_le. apply x. eapply Rplus_lt_weaken_rl.
  timeNonneg. delPos.
Qed.
  (*Note: This proof is similar to instant_insuff_abort except uses
  (incomp_incomingNet_abort) and (msgAbort_not_nextSince).*)

(** If a message was received some non-zero time t' ago and for longer than this time
we have been pending transition to a mode which threatens to be incompatible with
the received mode, given our current position & adjusting for time, the we get a
contradiction.*)
Theorem incomp_abort (n : Network) (t t' : Time) (l l' : Position) (i : nat)
  (m m' : Mode) (p : reachableProtNet n) :
  nextSince m t i n p -> inPosNet l i n ->
  received [baseMode m', basePosition l'] t' i n p -> zeroTime < t' -> t' < t ->
  dist2d l l' -nn- speedMax *nn* msgLatency + speedMax*t' < possIncDist m m' ->
  False.
Proof.
  intros U0 U1 U2 U3 U4 U5. 
  (*First, we show that 0 < t because t' < t.*)
  assert (0 < t). eapply Rle_lt_trans;[ |apply U4]. timeNonneg.
  (*The induction on received.*)
  generalize dependent t. generalize dependent l.
  dependent induction U2; intros l0 Y0 Y1 u U4 W0 W1.
  (*Base case is a contradiction because 0 < t'*)
  contradict U3. apply Rlt_irrefl.
  (*Discrete inductive case.*)
  dependent destruction U4. eapply Rlt_irrefl. eapply Rlt_trans. apply U3.
  assumption. assert (inPosNet l0 i n) as IP. inposdp.
  eapply IHU2; try assumption. apply IP. assumption. apply U4. assumption. assumption.
  (*Timed inductive case: first off, let's get some preliminaries done.*)
  dependent destruction U4. lets IPX : inPos_del_bound_bkwd Y0 w.
  decompEx2 IPX l IP DI.
  assert (t < t0) as TT. simpl in W0. Rplus_lt_tac.
  assert (0 < t0) as TG. eapply Rle_lt_trans;[ |apply TT]. timeNonneg.
  (*Then case analysis on previous t, was it zero or not?*)
  assert (zeroTime <= t) as TZ. timeNonneg. apply Rle_lt_or_eq_dec in TZ.
  elim_intro TZ TZ1 TZ2.
  (*If so, then the I.H. can be applied.*)
  eapply IHU2; try assumption. apply IP.
  (* Now it's time to deal with this inequality, which is a bit messy due to subtraction
  over nonnegative reals.*)
  eapply Rle_lt_trans;[ | apply Y1]. 
  lets DT : dist_tri_ineq l l0 l'.
  simpl. rewrite Rmult_plus_distr_l. Rplus3_swap_2_3_free.
  apply Rplus_le_compat; [ | apply Rle_refl].
  eapply Rle_trans. eapply Rle_subNonnegTot_r.
  rewrite <- addNonnegFact in DT. apply DT. rewrite Rplus_comm.
  eapply Rle_trans. apply addNonneg_subNonnegTot_le_assoc.
  rewrite addNonnegFact. Rplus_le_tac.
  (*And now we just tidy up some other stuff.*)
  eassumption. assumption. assumption.
  (*Leaving us with the case where t = 0. Now, at the time of receipt of the message,
  we are pending consumption of the message, or processing it (instant_incomp_abort).*)
  apply timeEqR in TZ2. rewrite <- TZ2 in U2.
  (* Another annoying inequality to show.*)
  assert (dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m') as DP.
  eapply Rle_lt_trans;[ | apply Y1]. lets DT : dist_tri_ineq l l0 l'.
  simpl. rewrite Rmult_plus_distr_l. Rplus3_swap_2_3_free.
  apply Rplus_le_weaken_rr. apply Rmult_le_0_compat; apply cond_nonneg.
  eapply Rle_trans. eapply Rle_subNonnegTot_r.
  rewrite <- addNonnegFact in DT. apply DT. rewrite Rplus_comm.
  eapply Rle_trans. apply addNonneg_subNonnegTot_le_assoc.
  rewrite addNonnegFact. Rplus_le_tac.
  (* Now use the inequality just proved towards a contradiction.*)
  lets IC : instant_incomp_abort U4 IP TG U2 DP.
  (*However urgency in all three cases holds, giving us the required contradiction.*)
  destruct IC as [IN | [MA | MB]]. eapply incomingNet_urgent. apply p. apply IN. apply w.
  eapply msgAbortPathNet_urgent. eassumption. apply MA. apply w.
  eapply msgBadPathNet_urgent. eassumption. apply MB. apply w.
Qed.

(* A precursor to incomp_bad, this says that if a message was just received this instant
and it's possibly incompatible with the current mode and position, then either a) it is
pending consumption, b) the message in question is being processed along the "msgBadPath"
or c) we have initiated a transition to tfs, this instant or before.*)
Theorem instant_incomp_tfs (n : Network) (t : Time) (l l' : Position) (i : nat)
  (m m' : Mode) (p : reachableProtNet n) :
  ~ failSafe m -> currSince m t i n p -> inPosNet l i n -> 0 < t ->
  received [baseMode m', basePosition l'] zeroTime i n p ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n \/
  msgBadPathNet i n \/ exists t, tfs m t i n p.
Proof.
  intros NFS H H0 U. intros.
  (*Induction on received.*)
  dependent induction H1.
  (*Incoming is easy to show for the base case- it follows from the network semantics.*)
  left. eapply incoming_ent_net. eapply input_incomingEnt. apply H3. assumption.
  (*The bulk of thought goes to the discrete inductive case. First a trivial result to
  use later on*)
  assert (inPosNet l i n) as Z. eapply inPos_pres_disc. apply w. assumption.
  (*Well, since received and currSince share the same history, we can show that
  currSince m t i n p must hold for the previous state or nextSince m t i n p must hold.*)
  dependent destruction H.
  (*If nextSince holds, then we can show by (...auto...) that the action linking the states
  was a tau leaving the interface unchanged (star).*)
  invertClearAs3 H0 e F1 F2. invertClearAs3 H1 e' F3 F4.
  lets K : switchCurr_switchListen_net_link F1 F3 F2 F4 w.
  invertClearAs2 K K1 K2.
  (*We then apply (instant_incomp_abort) to yield incomingNetMsg <m', l'> i n  \/
  msgAbortPath <m', l'> i n \/ msgBadPath <m', l'> i n.*)
  lets II : instant_incomp_abort H Z U H3 H4.
  (*The case of incomingNet is easy, because interface is has been shown to be preserved*)
  elim_intro II IN MAB. left.
  apply incoming_net_ent in IN. invertClearAs2 IN e0 IN2. invertClearAs2 IN2 IE X.
  invertClear IE. destruct e' as [P' l0' h' K']. eapply incoming_ent_net.
  constructor. apply H0. my_applys_eq F4. f_equal; try reflexivity.
  simpl in K2. rewrite <- K2. replace e with e0. rewrite <- H1. reflexivity.
  eapply entInNetUnique. apply X. assumption.
  (*The cases of msgAbortPath and msgBadPath yield a contradiction: we know that since a
  switch from nextSince to currSince occurred, then we are in a switchState. So then by
  (paused_switch_ent) we have that we are paused.*)
  assert (switchStateNet i n) as SS. econstructor. apply switchCurr_switch_ent.
  apply F1. assumption. rewrite <- (paused_switch_net n i p) in SS.
  (*But paused is disjoint from a msgAbortState and from a msgBadState (...auto...), hence
  the contradiction.*)
  false. destruct MAB as [MA | MB]. eapply msgAbort_paused_disj_net. apply MA. assumption.
  eapply msgBad_paused_disj_net. apply MB. assumption.
  (*So now we must prove our goal for the case in which the previous state was currSince.
  Here we can apply the I.H.*)
  assert ({| time := zeroNonneg |} = zeroTime) as V. reflexivity.
  lets IH : IHreceived H Z V H3. clear IHreceived.
  (*We can also show that currMode m i n by (currSince_curr).*)
  assert (currModeNet m i n) as J. eapply currSince_curr. apply H.
  (*Now we case analyse on the IH*)
  destruct IH as [IN | [MB | [t1 TF]]].
  (*Now, if the previous state was incomingNet, then we show by (incomp_incomingNet_bad) that
  one of the first two disjuncts holds, and we're done.*)
  lets IIB : (>> incomp_incomingNet_bad p w Z J IN H3). elim_intro IIB IB1 IB2.
  left. assumption. right. left. assumption.
  (*If msgBadPath holds, then we can show elsewhere that it is either preserved or goes to
  a tfs state, where the entity is tfs m for some time, both of which satisfy our goal.*)
  lets MD : msgBad_disc_net p w MB. elim_intro MD MD1 MD2. right. left. assumption.
  right. right. apply tfsState_tfs_exists; assumption.
  (*We can also show that tfs in turn is preserved.*)
  right. right. exists t1. apply tfsDisc; [exact TF | ].
  eapply (tfs_currMode_disc_pres n n' a i m); [exact p | exact w | exact J | exact NFS | ].
  eapply tfs_rel_state. exact TF.
  (*The delay inductive case can be thrown out because the time parameter to received is 0.*)
  assert (0 < t0 + d) as Q. apply Rplus_lt_weaken_rl. timeNonneg.
  delPos. rewrite <- x in Q. false. eapply Rlt_irrefl. apply Q.
Qed.

(* If we have been in the current mode m since time t, and we receive a message
with mode m' and position l0 some non-zero t' time units ago, with t' being
more recent than t, and the following inequality holds, with l our current
position: (|l - l0| - Smax*mL) + Smax*t' < Dpi m1 m2, then we have been tfs m for at
least t'.*)
Theorem incomp_tfs  (n : Network) (t t' : Time) (l l' : Position) (i : nat)
  (m m' : Mode) (p : reachableProtNet n) :
  ~ failSafe m -> currSince m t i n p -> inPosNet l i n ->
  received [baseMode m', basePosition l'] t' i n p ->
  zeroTime < t' -> t' < t  ->
  dist2d l l' -nn- speedMax*nn*msgLatency + speedMax*t' < possIncDist m m' ->
  exists (t'' : Time), t' <= t'' /\ tfs m t'' i n p.
Proof.
  intros NFS CS IP RC POS LT DI.
  revert t l CS IP LT DI POS.
  (*Induction on received.*)
  induction RC as [a i0 n0 n1 p0 w0 e e' l0 r E E' S | a t0 i0 n0 n1 p0 w0 RC IH
    | d t0 i0 n0 n1 p0 w0 RC IH]; intros t l CS IP LT DI POS.
  - (*In the base case t' is 0.*)
    exfalso. eapply Rlt_irrefl. exact POS.
  - (*The discrete case: currSince came from nextSince, which (incomp_abort) excludes, or
    from currSince, where the I.H. applies, and the entity stays in a tfs state
    (tfsState_not_currSince).*)
    assert (IPn : inPosNet l i0 n0) by (erewrite inPos_pres_disc; [exact IP | exact w0]).
    dependent destruction CS.
    + exfalso. eapply incomp_abort; eassumption.
    + destruct (IH t l CS IPn LT DI POS) as [t'' [LE TF]].
      exists t''. split; [exact LE | ]. apply tfsDisc; [exact TF | ].
      match goal with |- tfsStateNet ?j ?nn =>
        destruct (tfsStateNet_dec j nn) as [TS | NTS]; [exact TS | exfalso] end.
      match goal with [W : _ -NA- _ -NA> _ |- _] =>
        exact (tfsState_not_currSince _ _ _ _ _ _ _ W NFS (tfs_rel_state _ _ _ _ _ TF) NTS CS)
      end.
  - (*The timed case: by the speed bound and the triangle inequality, the inequality held
    before the delay, at the position l1 then and for t' less the delay. If that is not zero,
    the I.H. applies. If it is, (instant_incomp_tfs) applies, and since a pending message and
    the message bad path are urgent (incomingNet_urgent, msgBadPathNet_urgent), the entity
    is tfs.*)
    dependent destruction CS.
    destruct (inPos_del_bound_bkwd n0 n' d l i IP w0) as [l1 [IP1 BD]].
    lets TRI : dist_tri_ineq l1 l l'.
    assert (SH : dist2d l1 l' -nn- speedMax *nn* msgLatency <=
      speedMax * d + (dist2d l l' -nn- speedMax *nn* msgLatency)).
    { rewrite <- addNonnegFact in TRI.
      eapply Rle_trans; [exact (Rle_subNonnegTot_r _ _ (speedMax *nn* msgLatency) TRI) | ].
      eapply Rle_trans; [apply addNonneg_subNonnegTot_le_assoc | ].
      rewrite addNonnegFact. apply Rplus_le_compat_r. exact BD. }
    assert (DI1 : dist2d l1 l' -nn- speedMax *nn* msgLatency + speedMax * t0 <
      possIncDist m m').
    { clear - SH DI. destruct d as [[dd DP]]. simpl in *. nra. }
    assert (LT1 : t0 < t) by (clear - LT; destruct d as [[dd DP]]; simpl in *; lra).
    assert (Z : 0 <= t0) by timeNonneg. apply Rle_lt_or_eq_dec in Z.
    destruct Z as [Z | Z].
    + destruct (IH t l1 CS IP1 LT1 DI1 Z) as [t'' [LE TF]].
      exists (t'' +dt+ d). split; [ | apply tfsDel; exact TF].
      clear - LE. destruct d as [[dd DP]]. simpl in *. lra.
    + symmetry in Z. apply timeZero in Z. subst t0.
      assert (DI0 : dist2d l1 l' -nn- speedMax *nn* msgLatency < possIncDist m m').
      { clear - DI1. simpl in DI1. lra. }
      assert (T0 : 0 < t) by (clear - LT; destruct d as [[dd DP]]; simpl in *; lra).
      destruct (instant_incomp_tfs n0 t l1 l' i m m' p0 NFS CS IP1 T0 RC DI0)
        as [IN | [MB | [t2 TF]]].
      * exfalso. eapply incomingNet_urgent; [exact p0 | exact IN | exact w0].
      * exfalso. eapply msgBadPathNet_urgent; [exact p0 | exact MB | exact w0].
      * exists (t2 +dt+ d). split; [ | apply tfsDel; exact TF].
        assert (T2 : 0 <= t2) by timeNonneg. clear - T2. destruct d as [[dd DP]].
        simpl in *. lra.
Qed.

End NARIncomp.
