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
  msgAbortPathNet i n' \/ ~nextSinceStateNet i n'. introz U.
  (*Link down to the entity level and eliminate the entity equality case.*)
  inversion U. link_netentdiscfwd_tac e' b U1. left. econstructor.
  apply H. rewrite U2. assumption.
  (*Apply linking from the entity transition to the software transition.*)
  link_entsoftdisc_tac;
  (*Show and use equality between mode states.*)
  lets MSI : minet H0; lets MSI' : minet U1;
  lets NME : msgAbort_modeState_eq U MSI U0;
  lets MIU : mState_in_net_unique MSI' NME; subst.
  (*First deal with the case where the process terms are equal.*)
  left. econstructor;[ | apply U1].
  ent_disc_pres_pos_tac. subst.
  eapply msgAbort_inter_irrel. eassumption.
  (*Now on to the case where the process term transitions.*)
  remember (currModeMState k0) as CMM.
  (*Invert the path predicate and solve all 4 sub-cases.*)
  inversion H; ent_disc_pres_pos_tac; try unfold_all r'; subst. 
  (*---------------------Case 1: gotMsg -----------------*) 
  (*Then dive into the gotMsg state predicate to the lowest level and sovle this
  thing with tracking etc.*)
  inversion H6; subst.
  link_partripdiscex_tac_norm. 
  link_partripdiscW3_tac H1 LPT. elim_intro LPT EQP EXP.
  (*EQ case, LHS follows directly*)
  left. subst. econstructor;[ | apply U1].
  eapply mapMsg; try eassumption. econstructor. eassumption.
  reflexivity.
  (*transition case- need to use fwd-tracking.*)
  ex_flat. lets GMN : gotMessage_next H3 H2. ex_flat.
  (*Lift state predicates to entity level.*)
  assert (gotMsgStateEnt m'' l' ([|p1 $||$ p2 $||$ p3, l, h0, k0|])) as GME.
  constructor. assumption.
  assert (gotRangeStateEnt m'' x1 ([|p1' $||$ p2' $||$ p3', l, h, k0|])) as GRE.
  do 2 constructor. assumption.
  (*Add entit-level tracking result.*)
  lets GGE : gotMsg_gotRange_track_ent GME GRE U3. 
  (*Now we have msgAbortPath from the constructor.*)
  exand_flat. left. econstructor;[ | eassumption].
  eapply mapGrng. econstructor. eassumption. reflexivity.
  rewrite AND2. unfold not. intros. apply H8.
  assumption. eassumption. rewrite AND2. assumption.
  (*---------------------Case 2: gotRange -----------------*) 
  (*Then dive into the gotMsg state predicate to the lowest level and sovle this
  thing with tracking etc.*)
  inversion H6; subst.
  link_partripdiscex_tac_norm. 
  link_partripdiscW3_tac H1 LPT. elim_intro LPT EQP EXP.
  (*EQ case, LHS follows directly*)
  left. subst. econstructor;[ | apply U1].
  eapply mapGrng; try eassumption. econstructor. eassumption.
  reflexivity.
  (*transition case- need to use fwd-tracking.*)
  ex_flat.
  (*Lift the state predicate to the entity level and track it across the step: the listener
  is still in gotRange, or it read the current mode and is in currPincCheck with it.*)
  assert (gotRangeStateEnt m'' r ([|p1 $||$ p2 $||$ p3, l, h0, k0|])) as GRE.
  constructor. assumption.
  lets RE : reachable_net_ent rn H0.
  lets GGE : gotRange_track_ent RE GRE U3. elim_intro GGE GRE' CPC.
  (*Still gotRange: the path is preserved.*)
  ent_state_comp GRE'. left. econstructor;[ | apply U1].
  eapply mapGrng; try eassumption. econstructor. eassumption. reflexivity.
  (*currPincCheck with the current mode: the condition is false, so currComp follows.*)
  ent_state_comp CPC. simpl in CPC.
  left. econstructor. eapply mapCuco. econstructor.
  eapply currPincCheck_cond_false. apply H8. exact CPC.
  eassumption. assumption. eassumption.
  (*---------------------Case 3: currComp -----------------*) 
  (*Then dive into the gotMsg state predicate to the lowest level and sovle this
  thing with tracking etc.*)
  inversion H5; subst.
  link_partripdiscex_tac_norm. 
  link_partripdiscW3_tac H1 LPT. elim_intro LPT EQP EXP.
  (*EQ case, LHS follows directly*)
  left. subst. econstructor;[ | apply U1].
  eapply mapCuco; try eassumption. econstructor. eassumption.
  (*transition case- need to use fwd-tracking.*)
  ex_flat. lets GMN : currComp_next H3 H2.
  (*Two future cases, branch our goal at this point, but first prove a common
  entity level state predicate.*)
  assert (currCompStateEnt m'' r ([|p1 $||$ p2 $||$ p3, l, h0, k0|])) as CCE.
  constructor. assumption. elim_intro GMN ENP LSP.
  (*Sub-case 1: a msgAbortPath future of nextPincCheck.
  Lift state predicates to entity level.*)
  ex_flat.
  assert (nextPincCheckStateEnt x1 m'' r ([|p1' $||$ p2' $||$ p3', l, h, k0|])) as NPC.
  do 2 constructor. assumption.
  (*Add entity-level tracking result.*)
  lets GGE : currComp_nextPincCheck_track_ent CCE NPC U3. 
  (*Now we have msgAbortPath from the constructor.*)
  exand_flat. left. econstructor;[ | apply U1]. eapply mapAbort.
  econstructor. eapply nextPincCheck_cond_true. eassumption.
  rewrite H7 in AND2. inversion AND2. assumption.
  (*Sub-case 2: eliminate listeningState p3' by entity level theorem saying that
   currOKEnt ----> listeningEnt implies that the mode state is stable:
  which gives a contradiciton with nextModeMState k0 = Some m'*)
  assert (listeningStateEnt ([|p1' $||$ p2' $||$ p3', l, h, k0|])) as LSE.
  do 2 constructor. assumption.
  assert (unstable k0) as USK. eapply nextMode_unstable. eassumption.
  lets USO : unstable_stable_out_not USK. false. apply USO.
  econstructor. lets CLT : currComp_listening_track_ent CCE LSE U3. 
  and_flat. eassumption.
  (*---------------------Case 4: abortOvlp, final case -----------------*) 
  (** This case is almost identical to the case for notifAbortPath_not_nextSince.*)
  inversion H3; subst. link_partripdiscex_tac_norm. swapRename H1 H2.
  link_partripdiscW3_tac H2 LPT. elim_intro LPT EQP EXP.
  (*EQ case, LHS follows directly*)
  left. subst. econstructor;[ | apply U1].
  eapply mapAbort. econstructor. eassumption.
  (*transition case- need to use fwd-tracking.*)
  ex_flat. lets CON : abortOvlp_next H4 H1. right.
  (*Assert some useful results for later.*)
  assert (p3 <> p3') as PNE3. unfold not. intros. subst.
  false. eapply listening_abort_contra; eassumption.
  assert (p1 $||$ p2 $||$ p3 <> p1' $||$ p2' $||$ p3') as PNE.
  unfold not. intro. inversion H5. subst. apply PNE3. reflexivity.
  (*apply ent proc link theorem and flatten out the ands, ors and exists.*)
  lets LEP : link_ent_proc_neq_disc PNE U3. andflat LEP.
  or_flat; ex_flat; and_flat; try link_partripneq_tac;
  try (lets CLT : abortOvlp_listening_track H1 CON AND1; inversion CLT); subst.
  (*In the first case apply this tactic: link_partriptau_tac,
  and use tracking to narrow down info and eliminate some cases.*)
  reach_net_prot_tac. link_partriptau_tac c v LPT;
  try (lets CLT : abortOvlp_listening_track H1 CON LPT1;
  inversion CLT; subst).
  (*Eliminate first two sub-cases by contradiction.*)
  subst; contradict PNE3; reflexivity.
  subst; contradict PNE3; reflexivity.
  (*Two remaining sub-cases are that p1 or p2 output on MStable.
  Contradictions can be shown in both cases.*)
  false. eapply bc_abort_in_not. apply LPT.
  inversion RPT. assumption.
  (*This is the special case, where we need to show that nextSinceState does not hold.*) 
  inversion RPT.
  lets OAI : ovlp_abort_in_notNextSince LPT H9. unfold not. intro. apply OAI.
  inversion H11. entnetuniq2 EN n'. subst. inversion H12. inversion H6.
  assumption.
  (*Now back to the remaining cases. First eliminate interface/software synch.*)
  false. eapply inter_abort_in_not. eassumption.
  (*Then do the modeState/software synch.*)
  false. eapply modeState_abort_in_not; eassumption.
  (*Get rid of p reading current position by tracking and showing that actions can't be equal-
  incompatible actions in question are input on pos and input on stable*)
  lets CLT : abortOvlp_listening_track H1 CON AND; inversion CLT. Qed.

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