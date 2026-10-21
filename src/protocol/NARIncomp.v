(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Program.Equality.
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
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.NARMisc.
Require Import ComhCoq.protocol.ProtocolBridge.


(*If any entity has an incomingNet message the network can't delay.*)
Theorem incomingNet_urgent (n n' : Network) (v : list BaseType) (i : nat) (d : Delay) :
  reachableProtNet n -> incomingNet v i n -> ~n -ND- d -ND> n'. Admitted. (*3*)
(**Proof: First we show by inversion on incomingNet v i n that there is some e @ i .: n.
Now assume there was such a del towards a contradiction. Then by (del_listening) we'd have
listeningState i n. But then it can be shown by (...listening-inProc...) that the software
component is capable of consuming any pending message. So a tau can happen by synchronidastion
with the incomingNet message- this may be a separate result. So by [maximal progress- salvaged?
a delay is not possible, contradicting the earlier assumtion.*)

(*If an incoming message is incompatible with the current mode & the position,
then in the next state, it is either still incoming or we have entered the msgBadPath.*)
Theorem incomp_incomingNet_bad (n n' : Network) (a : ActDiscNet) (l l' : Position) (i : nat)
  (m m' : Mode) :
  n -NA- a -NA> n' -> inPosNet l i n -> currModeNet m i n ->
  incomingNet [baseMode m', basePosition l'] i n ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n' \/
  msgBadPathNet i n'.
  introz U. 
  destruct U2.
  link_netentdiscfwd_tac e' a' Y. destr_ent_inter e' p' l'' k' li' lo' ln'.
  (*If the entity hasn't changed, then incoming is preserved*)
  left. eapply incoming_ent_net. repeat constructor. apply H0. my_applys_eq Y.
  symmetry. apply Y0. 
  (*Otherwise the entity has performed a transition to another entity, which we destruct.*)
  destruct e' as [p' l'' h' k'].
  (*Now we analyse the different cases for the interface that match this
  entity transition.*)
  link_entinterdisc_tac v r Q;destruct h' as [li' lo' ln'];
  try ((*First lets assert that the action we have is not a delay, for use later.*)
  match goal with [TRI : _ -i- ?act -i> _ |- _] =>
  assert (forall d : Delay, act <> d) as ANE end; [intro d;
  unfold not; intro CON; inversion CON | ]);
  try solve
  [lets W : inList_inter_pres_input ANE H0 Q; elim_intro W W1 W2;[left; eapply incoming_ent_net;
  repeat constructor; [apply W1 | apply Y] | inversion W2]].
  (*If the interface hasn't changed then incoming is preserved, similar to previous argument*)
  left. eapply incoming_ent_net. repeat constructor. apply H0. my_applys_eq Y.
  rewrite <- Q. reflexivity.
  (*So we're left only with the case where the process inputs v on inProc. Now we just need
  eliminte the case where the message is different to the one buffered*)
  lets II : inList_inter_pres_input ANE H0 Q. elim_intro II IN EQ. left.
  eapply incoming_ent_net. repeat constructor. apply IN. apply Y.
  inversion EQ. 
  (*So now we know that the process inputs m, l on inProc*)
  invertClearAs1 EQ EB. rewrite EB in Q0. 
  (*Here, from a separate result we can show the first case of msgBadPath.*)
  right. doappsnd econstructor Y. lets GM : gotMsg_state Q0.
  lets CX : U1. rewrite currMode_ent_ex in CX. decompExAnd CX e EA EM.
  lets EU : entInNetUnique EA H. rewrite EU in EM.
  lets MB : mbpMsg GM EM U3.
  replace l'' with l. rewrite <- H3. eapply MB.
  eapply inPos_unique. rewrite <- inPos_pres_disc. apply U0. apply U.
  econstructor. apply Y. Qed.
  (*If the action a is not an input of [m, l], then [m, l] must
  still be contained in the input list. Then show that if a is such an input, the
  base case for msgBadPathNet is satisfied.*)

(**If an incomingNet message is incompatible with the
next mode & the position, then in the next state, it is either still incomingNet
or we have entered the msgAbortPath.*)
Theorem incomp_incomingNet_abort (n n' : Network) (a : ActDiscNet) (l l' : Position) (i : nat)
  (m m' : Mode) : n -NA- a -NA> n' -> inPosNet l i n -> nextModeNet m i n ->
  incomingNet [baseMode m', basePosition l'] i n ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n' \/ msgAbortPathNet i n'.
  Admitted. (*3*)

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

(* This says that if a message was just received this instant
and it's possibly incompatible with the  pending mode and position,
then either a) it is pending consumption or b) the message in question
is being processed along the "msgAbortPath".*)
Theorem instant_incomp_abort (n : Network) (t : Time) (l l' : Position) (i : nat)
  (m m' : Mode) (p : reachableProtNet n) :
  nextSince m t i n p -> inPosNet l i n -> 0 < t ->
  received [baseMode m', basePosition l'] zeroTime i n p ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n  \/
  msgAbortPathNet i n.
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
  msgAbortPath m r i n.*)
  lets IHdisc : IHU1 U IP TZ U2. clear IHU1.
  (*Now we do a case analysis on this disjunction.*)
  elim_intro IHdisc IN MA.
  (*First off we have incomingNet <r, m, l> 0 i n. We can show then by
  (incomp_incomingNet_abort) that our goal holds in the next state.*)
  assert (nextModeNet m i n) as NM. eapply nextSince_next. apply U.
  lets II : incomp_incomingNet_abort w IP NM IN U2. apply II.
  (*Then there's the case where msgAbortPath m r i n. In this case, we can show by
  (msgAbort_not_nextSince) that either msgAbortPath m r i n' or ~nextSineState m i n'.*)
  lets MN : msgAbort_not_nextSince p MA w. elim_intro MN MP NS.
  (*The former gives us our goal by the RHS.*)
  right. assumption.
  (*The latter gives us a contradiction by nextSinceState*)
  false.
  (*Delay case: contradicion, the time parameter to received was assumed to be 0*)
  false. eapply Rle_not_lt. apply Req_le. apply x. eapply Rplus_lt_weaken_rl.
  timeNonneg. delPos. Qed.
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
  (*However urgency in both cases holds, giving us the required contradiction.*)
  elim_intro IC IN MA. eapply incomingNet_urgent. apply p. apply IN. apply w.
  eapply msgAbortPathNet_urgent. eassumption. apply MA. apply w. Qed.

(* A precursor to incomp_bad, this says that if a message was just received this instant
and it's possibly incompatible with the current mode and position, then either a) it is
pending consumption, b) the message in question is being processed along the "msgBadPath"
or c) we have initiated a transition to tfs this instant.*)
Theorem instant_incomp_tfs (n : Network) (t : Time) (l l' : Position) (i : nat)
  (m m' : Mode) (p : reachableProtNet n) :
  ~ failSafe m -> currSince m t i n p -> inPosNet l i n -> 0 < t ->
  received [baseMode m', basePosition l'] zeroTime i n p ->
  dist2d l l' -nn- speedMax *nn* msgLatency < possIncDist m m' ->
  incomingNet [baseMode m', basePosition l'] i n \/
  msgBadPathNet i n \/ tfs m zeroTime i n p.
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
  msgAbortPath <m', l'> i n.*)
  lets II : instant_incomp_abort H Z U H3 H4.
  (*The case of incomingNet is easy, because interface is has been shown to be preserved*)
  elim_intro II IN MA. left.  
  apply incoming_net_ent in IN. invertClearAs2 IN e0 IN2. invertClearAs2 IN2 IE X.
  invertClear IE. destruct e' as [P' l0' h' K']. eapply incoming_ent_net.
  constructor. apply H0. my_applys_eq F4. f_equal; try reflexivity.
  simpl in K2. rewrite <- K2. replace e with e0. rewrite <- H1. reflexivity.
  eapply entInNetUnique. apply X. assumption.
  (*The case of msgAbortPath yields a contradiction: we know that since a switch from
  nextSince to currSince occurred, then we are in a switchState. So then by
  (PA::paused_switch) we have that we are paused.*)
  assert (switchStateNet i n) as SS. econstructor. apply switchCurr_switch_ent.
  apply F1. assumption. rewrite <- (paused_switch_net n i p) in SS.
  (*But paused is disjoint from a msgAbortState (...auto...), hence the contradiction.*)
  false. eapply msgAbort_paused_disj_net. apply MA. assumption.
  (*So now we must prove our goal for the case in which the previous state was currSince.
  Here we can apply the I.H.*)
  assert ({| time := zeroNonneg |} = zeroTime) as V. reflexivity.
  lets IH : IHreceived H Z V H3. clear IHreceived.
  (*We can also show that currMode m i n by (currSince_curr).*)
  assert (currModeNet m i n) as J. eapply currSince_curr. apply H.
  (*Now we case analyse on the IH*)
  decompose [or] IH; clear IH.
  (*Now, if the previous state was incomingNet, then we show by (incomp_incomingNet_bad) that
  one of the first two disjuncts holds, and we're done.*)
  lets IIB : incomp_incomingNet_bad w Z J H4 H3. elim_intro IIB IB1 IB2.
  left. assumption. right. left. assumption.
  (*If msgBadPath holds, then we can show elsewhere that it is either preserved or goes to
  tfs m 0 i n p, both of which satisfy our goal.*)
  lets MD : msgBad_disc_net p w H5 J. elim_intro MD MD1 MD2. right. left. assumption.
  right. right. apply MD2.
  (*We can also show that tfs in turn is preserved with time 0.*)
  right. right. apply tfs_zero_disc_pres; [exact J | exact NFS | assumption].
  (*The delay inductive case can be thrown out because the time parameter to received is 0.*)
  assert (0 < t0 + d) as Q. apply Rplus_lt_weaken_rl. timeNonneg.
  delPos. rewrite <- x in Q. false. eapply Rlt_irrefl. apply Q. Qed.

(*NEED TO RE-DO THE TRIANGLE INEQUALITY STUFF IN LIGHT OF THE SWITCH TO THE USE
OF THE TOTAL FUNCTION FOR SUBTRACTION.*)
(* If we have been in the current mode m since time t, and we receive a message
with mode m' and position l0 some non-zero t' time units ago, with t' being
more recent than t, and the following inequality holds, with l our current
position: (|l - l0| - Smax*mL) + Smax*t' < Dpi m1 m2, then we are tfs m t'.*)
Theorem incomp_tfs  (n : Network) (t t' : Time) (l l' : Position) (i : nat)
  (m m' : Mode) (p : reachableProtNet n) :
  ~ failSafe m -> currSince m t i n p -> inPosNet l i n ->
  received [baseMode m', basePosition l'] t' i n p ->
  zeroTime < t' -> t' < t  ->
  dist2d l l' -nn- speedMax*nn*msgLatency + speedMax*t' < possIncDist m m' ->
  tfs m t' i n p. intro NFS. intros.
  (*We first need to show that speedMax * t is less than possIncDist m m' in order
  to be able to apply a special equivalence result later for our (annoying!)
  subNonnegTot function.*)
  assert (speedMax * t' < possIncDist m m') as TLP. eapply Rle_lt_trans;
  [ | apply H4]. Rplus_le_tac. apply cond_nonneg.  
  (*And then we're back to our proof, which goes smoothly let's hope!*)
  generalize dependent t. generalize dependent l.
  induction H1; intros; rename t into t'.
  contradict H2. apply Rlt_irrefl.
  (*The discrete inductive case carries over easily.*)
  (*First we notice that position is preserved*)
  assert (inPosNet l i n). erewrite inPos_pres_disc. apply H0. apply w.
  (*Now we backtrack from currSince and first eliminate the nextSince case.*)
  dependent destruction H. apply False_ind. eapply incomp_abort. apply H.
  apply H7. apply H1. assumption. assumption. assumption.
  (*Then we show the currSince case to hold*)
  addHyp (IHreceived H2 TLP l H6 H4 t H H5). clear IHreceived. 
  constructor. assumption. apply tfs_rel_state in H7. addHyp (tfsStateNet_dec i n').
  appDisj H8. apply False_ind. eapply tfsState_not_currSince. apply w.
  apply NFS. apply H7. assumption. apply H.
  (*Now for the timed case. We first observe that currSince carries to the previous
  state because it is preserved backwards by delay*)
  dependent destruction H. 
  (*We then split our reasoning into two cases. One where in the previous case
  t', the parameter to received is non-zero, the other where it is 0.*)
  assert (0 <= t'). timeNonneg. apply Rle_lt_or_eq_dec in H5.
  invertClear H5.
  (*If t' is non zero, we must look at the old position, call it l1. Now we know by
  [pos_bound salvaged?] that |l1 - l| <= Smax*d (star).*)
  addHyp (inPos_del_bound_bkwd n n' d l i H0 w). decompose [ex] H5. clear H5.
  rename x into l1. invertClear H7. 
  (*Then from the (triangle inequality) we have that |l1 - l'| <= |l1 - l| + |l - l'|.
  (&&)*)
  addHyp (dist_tri_ineq l1 l l').
  (*But from our assumption we have that |l - l'| - Smax*mL + Smax*(t' + d) < Dpi m m'.
  Adding this to (star) we get
  |l1 - l| + |l - l'| - Smax*mL + Smax*(t' + d) < Dpi m m' + Smax*d.*)
  (*Convert H4 from subNonnegTot to Rminus*)
  apply subNonnegTot_plus_lt_Rminus in H4.
  addHyp (Rplus_le_lt_compat (dist2d l1 l) (speedMax * d)
  (dist2d l l' - speedMax * msgLatency + speedMax * (t' +dt+ d))
  (possIncDist m m') H8 H4).
  (*A bit of algebra allows us to cancel the Smax*d on both sides, giving
  |l1 - l| + |l - l'| - Smax*mL + Smax*t' < Dpi m m' (@).*)
  replace (nonneg (dist2d l1 l) +
  (nonneg (dist2d l l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * pos (delay (t' +dt+ d)))) with (nonneg (dist2d l1 l) +
  nonneg (dist2d l l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * (nonneg t') + nonneg speedMax * pos(delay d)) in H9;
  [ |simpl;ring]. replace (nonneg speedMax * pos (delay d) + possIncDist m m')
  with (possIncDist m m' + nonneg speedMax * pos (delay d)) in H9;[ |ring].
  apply Rplus_lt_reg_r in H9.
  (*Then adding - Smax*mL + Smax*t' to (&&) we get
  |l1 - l'| - Smax*mL + Smax*t' <= |l1 - l| + |l - l'| - Smax*mL + Smax*t'.*)
  apply (Rplus_le_compat_r (-speedMax*msgLatency + speedMax*t')) in H7.
  (*By transitivity on (@) then we have |l1 - l'| - Smax*mL + Smax*t' < Dpi m m'.*)
  assert (nonneg (dist2d l1 l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t') < possIncDist m m'). eapply Rle_lt_trans.
  eapply Rle_trans;[ | apply H7]. apply Req_le. ring.
  eapply Rle_lt_trans;[ | apply H9]. apply Req_le. ring.
  (*Now we can apply the I.H. yielding tfs m t' i n p, which by application of the
  tfs delay constructor gives the required tfs m (t' + d) i n p.*)
  constructor. apply IHreceived with (t := t) (l := l1); try assumption. 
  eapply Rplus_lt_reg_l. eapply Rlt_le_trans. my_applys_eq TLP.
  simpl. rewrite Rmult_plus_distr_l.
  (*Unclear what happened this result. Proof used to work:
  reflexivity. Rplus_le_tac.
  apply Rmult_le_pos. apply cond_nonneg. apply Rlt_le. delPos.
  (*Here we apply a special result to get rid of the niggly -nn- and make it a nice
  normal -.*)
  apply Rminus_plus_lt_subNonnegTot. eapply Rle_lt_trans;[ | apply TLP].
  simpl. rewrite Rmult_plus_distr_l. Rplus_le_tac. apply Rmult_le_pos.
  apply cond_nonneg. apply Rlt_le. delPos.
  (*And now back to the proof as normal.*)
  assumption. eapply Rplus_lt_reg_l. apply H3.
  (*We are then left with the case where t' = 0. Now, by the same argument as
  before involving the (triangle inequality), we have that
  |l1 - l'| - Smax*mL + Smax*t' < Dpi m m'*)
  addHyp (inPos_del_bound_bkwd n n' d l i H0 w). decompose [ex] H5. clear H5.
  rename x into l1. invertClear H7. 
  addHyp (dist_tri_ineq l1 l l').
  (*Here we use a special result to convert the niggly -nn- and make it a nice
  normal -.*)
  apply subNonnegTot_plus_lt_Rminus in H4.
  (*And now back to the proof as normal.*)
  addHyp (Rplus_le_lt_compat (dist2d l1 l) (speedMax * d)
  (dist2d l l' - speedMax * msgLatency + speedMax * (t' +dt+ d))
  (possIncDist m m') H8 H4).
  replace (nonneg (dist2d l1 l) +
  (nonneg (dist2d l l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * pos (delay (t' +dt+ d)))) with (nonneg (dist2d l1 l) +
  nonneg (dist2d l l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * (nonneg t') + nonneg speedMax * pos(delay d)) in H9;
  [ |simpl;ring]. replace (nonneg speedMax * pos (delay d) + possIncDist m m')
  with (possIncDist m m' + nonneg speedMax * pos (delay d)) in H9;[ |ring].
  apply Rplus_lt_reg_l in H9. 
  apply (Rplus_le_compat_r (-speedMax*msgLatency + speedMax*t')) in H7.
  assert (nonneg (dist2d l1 l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t') < possIncDist m m'). eapply Rle_lt_trans.
  eapply Rle_trans;[ | apply H7]. apply Req_le. ring.
  eapply Rle_lt_trans;[ | apply H9]. apply Req_le. ring.
  (*Now, with t' = 0 this gives us |l1 - l'| - Smax*mL < Dpi m m'.*)
  rewrite <- H6 in H10. rewrite Rmult_0_r in H10. rewrite Rplus_0_r in H10.
  (*Also by (@@) we have currSince for the previous state. From here we can
  apply (instant-incomp-tfs) to get incomingNet <m', l'> i n  \/
  msgBadPath <m', l'> i n \/ tfs m 0 i n p.*)
  symmetry in H6. apply timeZero in H6. rewrite H6 in H1.
  assert (0 < t) as U. simpl in H3. apply Rplus_lt_reg_l in H3.
  eapply Rle_lt_trans;[ |apply H3]. timeNonneg.
  (*Some stuff to get rid of annoying -nn-*)
  assert (0 < possIncDist m m') as ZPD. eapply Rle_lt_trans; [ | apply TLP].
  apply Rmult_le_pos. apply cond_nonneg. simpl. replace 0 with (0 + 0).
  apply Rplus_le_compat. timeNonneg. apply Rlt_le. delPos. ring.
  lets RLS : Rminus_lt_subNonnegTot ZPD.
  rewrite <- multNonneg_Rmult_eq in H10. apply RLS in H10.
  (*Back to the main proof.*)
  addHyp (instant_incomp_tfs n t l1 l' i m m' p NFS H H5 U H1 H10).
  decompose [or] H11; clear H11.
  (*The first two disjuncts fail because it can be shown that delay is
  impossible in these cases (incomingNet-urgent), (...EA::msgBadPath-urgent...).*)
  apply False_ind. eapply incomingNet_urgent. apply p. apply H12. apply w.
  apply False_ind. eapply msgBadPathNet_urgent. apply p. apply H13. apply w.
  (*Which leaves us with tfs m 0 i n p, and we can proceed immediately from this to
  our goal by one application of the tfs delay constructor.*)
  constructor. rewrite H6. assumption. Qed.*) Admitted.