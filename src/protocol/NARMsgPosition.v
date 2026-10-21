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
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults.
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.NARMisc. 
Require Import ComhCoq.protocol.ProtocolBridge.

Open Scope R_scope.

(* If an entity has sent a message v t time units ago, and that time is less than the 
message latency, then said message is in the output queue of the interface component 
with timestamp mL - t.*)
Theorem sent_outgoing (n : Network) (v : list BaseType) (t : Time) (i : nat)
  (p : reachableProtNet n) :
  sent v t i n p -> forall q : t < msgLatency,
  outgoing v (minusTime msgLatency t (Rlt_le t msgLatency q)) i n.
  (**Proof: Induction on sent.*)
  intros. induction H.
  (*In the base case we have that h - ioProc<v>? -> h', where h is the interface of the entity
  in question. By analysing this interface transition we get that <v, mL> is at the head of the
  output list of I', and so is in this list*)
  invertClear H2.
  addHyp (outList_received_in l2 l2' v H5).
  (*and so we have outgoing v mL i n, which is our goal exactly since t = 0.*)
  econstructor. rewrite <- H6 in H0.
  apply H0. replace (minusTime msgLatency zeroTime (Rlt_le zeroTime msgLatency q))
  with msgLatency. apply H2. apply timeEqR. simpl. ring.
  (*In the discrete case for induction we apply the I.H.*)
  addHyp (IHsent q). clear IHsent.
  (*Since t hasn't changed we get outgoing v (mL - t) i n. We then observe that since
  t < mL, then 0 < mL - t*)
  remember (minusTime msgLatency t (Rlt_le t msgLatency q)) as t'.
  assert (0 < t'). rewrite Heqt'. simpl. apply RltMinusBothSides. assumption.
  (*and so by (NetAuxBasics::outgoing_disc_pres) the outgoing relation is preserved
  from the previous to the current state, giving outgoing v (mL - t) i n' as required.*)
  addHyp (outgoing_disc_pres n n' a v t' i w H0 H1). assumption. 
  (*In the delay case for induction, we can immediately infer from  t + d < mL
  that t < mL and so outgoing v (mL - t) i n.*)
  simpl in q. assert (t < msgLatency). eapply Rplus_lt_weaken_lr. apply q. apply Rlt_le.
  delPos. addHyp (IHsent H0). clear IHsent.
  (*Then since n -d-> n', by (NetAuxBasics::outgoing_del) we get
  outgoing v (mL - t - d) i n = outgoing v (mL - (t + d)) i n, which is our goal exactly.*)
  remember (minusTime msgLatency t (Rlt_le t msgLatency H0)) as t'.
  addHyp (outgoing_del n n' d v t' i w H1). invertClear H2.
  replace (minusTime (nonneg (time msgLatency)) (nonneg (time (delToTime (t +dt+ d))))
  (Rlt_le (nonneg (time (delToTime (t +dt+ d)))) (nonneg (time msgLatency)) q)) with
  (minusTime t' d x). apply H3. clear H1 H3. generalize dependent x. rewrite Heqt'.
  intros. apply timeEqR. simpl. ring. Qed.

(*If an entity is nextSince m t, then <m, l0> was sent exactly t time units ago for some l0.*)
(* begin helpers for fst_sent *)
(*ovWait m' t' x y can input on abort.*)
Local Lemma ovWait_abort_in p m t x y : ovWaitState m t x y p -> discActEnabled p (chanAbort *?).
  activation_tac. Qed.

(*No process is both ovReady and ovWait: ovWait can input on abort but ovReady can't.*)
Local Lemma ovReady_not_ovWait p m t l m' t' x y :
  ovReadyState m t l p -> ovWaitState m' t' x y p -> False.
  intros U V. apply ovWait_abort_in in V. eapply bisim_dae in V;[ | apply U].
  inversion V. unfold ovReady in H. repeat invert_trans_rich. Qed.

Local Lemma ovReady_not_ovWait_prot q m t l m' t' x y :
  ovReadyStateProt m t l q -> ovWaitStateProt m' t' x y q -> False.
  intros U V. inversion U; subst. inversion V; subst.
  eapply ovReady_not_ovWait; eassumption. Qed.
(* end helpers *)

Theorem fst_sent (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableProtNet n) : nextSince m t i n p ->
  exists l0, sent [baseMode m, basePosition l0] t i n p.
Proof.
(**Proof: By induction on nextSince.*)
  intros. induction H.
  (*In the base case, the entity i goes from ovReady to ovWait.*)
  destruct H0 as [e E1 E2]. destruct H1 as [e' E1' E2'].
  destruct e as [q l1 h k]. destruct e' as [q' l1' h' k'].
  lets L : link_net_ent_disc w E2 E2'. destruct L as [EQ | [a' ST]].
  (*The entity can't be unchanged, because ovReady and ovWait are exclusive.*)
  inversion EQ; subst. inversion E1; inversion E1'; subst. false.
  eapply ovReady_not_ovWait_prot; eassumption.
  (*Tracking yields that the software component outputs <m, l> on outProc and the interface
  inputs it, with the mode state and position unchanged.*)
  lets T : ovReady_ovWait_track_ent E1 E1' ST. destruct T as [T1 [T2 [T3 [T4 T5]]]]. subst.
  lets PP : stepEnt_disc_pres_pos ST. simpl in PP. subst.
  (*The software term has changed, so the network action is a tau.*)
  assert (q <> q') as NE. intro. subst. inversion E1; inversion E1'; subst.
  eapply ovReady_not_ovWait_prot; eassumption.
  lets TAU : procNeq_tau_net E2 E2' w NE. subst.
  exists l1'. eapply sentBase; eassumption.
  (*In the inductive cases, we simply apply the inductive hypothesis and
  then the appropriate constructor of sent.*)
  destruct IHnextSince as [l0 S]. exists l0. constructor. assumption.
  destruct IHnextSince as [l0 S]. exists l0. constructor. assumption.
  Qed.

(* If an entity has sent a message v mL time units ago, then said message is in the output
queue of the interface component with timestamp 0 or it has been delivered 0 time units ago.*)
Theorem sent_out_del (n : Network) (v : list BaseType) (i : nat)
  (p : reachableProtNet n) : sent v msgLatency i n p ->
  outgoing v zeroTime i n \/
  exists r l, delivered ([-v, l, r-]) zeroTime i n p.
  (**Proof: By induction on sent.*)
  introz U. remember msgLatency as mL. induction U.
  (*The base case fails because it gives the contradiction mL = 0, while mL
  is assumed positive.*)
  false. eapply Rlt_not_le. apply msgLatency_positive. rewrite <- HeqmL.
  apply Rle_refl.
  (*For the discrete inductive case we get from the I.H. that either
  outgoing v 0 i n or delivered v r 0 i n.*)
  apply IHU in HeqmL. clear IHU. elim_intro HeqmL OZ EDZ.
  (*In the first case we know outgoing v 0 i n. In which case we can apply
  (Basics::outgoing_timeout_disc) to obtain our goal.*)
  (*First we just do a little bit of processing to explicitly get the entity
  and hence its position.*)
  lets OZX : OZ. inversion OZX as [q0 l li lo ln k EIN INO].
  assert (inPosNet l i n) as IP by (econstructor; eassumption).
  lets OTD : outgoing_timeout_disc IP OZ. or_flat.
  (*The left subcase immediately gives the goal.*)
  left. eassumption.
  (*The right sub-case gives the RHS of the goal.*)
  ex_flat. right. exists x. exists l. eassumption.
  (*If the latter is true, then we can immediately show by constructor
  that delivered v r 0 i n'.*)
  right. ex_flat. exists x x0. constructor. assumption.
  (*Moving on to the timed case, where we get that t + d = mL and so
  t = mL - d < mL*)
  assert (t < msgLatency). rewrite <- HeqmL. simpl. Rplus_lt_tac.
  delPos.
  (*From here, by (sent_outgoing) we have outgoing v (mL - t) i n*)
  lets SO : sent_outgoing U H. left.
  (*Now, by some algebra and substituting for t using our recently deduced
  equality is the same as outgoing v d i n.*)
  assert (outgoing v d i n) as OD. my_applys_eq SO. 
  apply timeEqR. simpl. rewrite <- HeqmL. simpl.
  destruct d. destruct delay. simpl. ring.
  (*Now we apply (Basics::outgoing_del)*)
  lets OGD : outgoing_del w OD. invertClear OGD.
  (*And we get a term equivalent to outgoing v 0 i n, as required.*)  
  my_applys_eq H0. apply timeEqR. simpl. destruct d; destruct delay.
  simpl. ring. Qed.

(* If an entity has sent a message v t time units ago, and that time is greater than the
message latency, then said message was delivered to some radius, and the delivery time
is less than the time of sending by the amount message latency.*)
Theorem sent_delivered (n : Network) (v : list BaseType) (t : Time) (i : nat)
  (p : reachableProtNet n) : sent v t i n p -> forall q : msgLatency < t,
  exists r l,
  delivered ([-v, l, r-]) (minusTime t msgLatency (Rlt_le msgLatency t q)) i n p.
  (**Proof: Induction on sent. Well the base case can be immediately discarded due to the
  contradiction of t = 0 and mL < t, given that mL is positive.*)
  intros. induction H. contradict q. apply Rle_not_lt. simpl. timeNonneg.
  (*In the discrete inductive case, the time parameter does not change since the previous
  state, and so by the inductive hypothesis we have delivered v r (t - mL) i n*)
  addHyp (IHsent q). clear IHsent. decompose [ex] H0. clear H0. rename x0 into l.
  rename x into r.
  (*Then by the discrete constructor of delivered we have in this state
  delivered v r (t - mL) i n'.*)
  exists r. exists l. constructor. assumption.
  (*For the timed case, there are two subcases.*)
  addHyp (Rlt_or_le msgLatency t). invertClear H0.  
  (*If mL < t, then by the inductive hypothesis and timed constructor of delivered we get
  our goal.*)
  addHyp (IHsent H1). clear IHsent. decompose [ex] H0. exists x. exists x0.
  replace (minusTime (nonneg (time (delToTime (t +dt+ d))))
  (nonneg (time msgLatency)) (Rlt_le (nonneg (time msgLatency))
  (nonneg (time (delToTime (t +dt+ d)))) q)) with
  (delToTime ((minusTime t msgLatency (Rlt_le msgLatency t H1)) +dt+ d)).
  apply deliveredDel. assumption. apply timeEqR. simpl. ring.
  (*Else, t <= mL. We split this again into t < mL and t = mL.*)
  apply Rle_lt_or_eq_dec in H1. invertClear H1.
  (*t < mL gives a contradiction. We achieve the contradiction by first applying
  (sent_outgoing) to get outgoing v (mL - t) i n.*)
  addHyp (sent_outgoing n v t i p H H0).
  (*Then we apply (NetAuxBasics::outgoing_del) to get d <= mL - t*)
  remember ((minusTime msgLatency t (Rlt_le t msgLatency H0))) as t'.
  addHyp (outgoing_del n n' d v t' i w H1).
  (*So t + d <= mL.*)
  invertClear H2. assert (t +dt+ d <= msgLatency). simpl. clear H3. rename x into Q.
  rewrite Heqt' in Q. simpl in Q.
  rewrite Rplus_comm. apply Rminus_le_swap_rr. assumption.
  (*But from our hypothesis we have mL < t + d, so we arrive at a contradiction.*)
  contradict q. apply Rle_not_lt. assumption.
  (*Thus we conclude t = mL and we can apply sent_out_del to our previous case, yielding
  outgoing v 0 i n \/ exists r, delivered v r 0 i n.*)
  apply timeEqR in H0. rewrite H0 in H. addHyp (sent_out_del n v i p H).
  invertClear H1.
  (*The LHS fails, again by contradiction via a corollary of (NetAuxBasics::outgoing_del)
  saying that t = 0 implies no delay is possible.*)
  addHyp (outgoing_del_contra n n' d v i w H2). inversion H1.
  (*So we conclude that delivered v r 0 i n for some r*)
  decompose [ex] H2. rename x0 into l. rename x into r. exists r.
  exists l.
  (*and then by the delay constructor of delivered we have our goal
  delivered v r (0 + d) i n'.*)
  replace (minusTime (nonneg (time (delToTime (t +dt+ d))))
  (nonneg (time msgLatency)) (Rlt_le (nonneg (time msgLatency))
  (nonneg (time (delToTime (t +dt+ d)))) q)) with
  (delToTime (zeroTime +dt+ d)).
  apply deliveredDel. assumption. apply timeEqR. simpl. rewrite H0. ring.
  (*Note that there are no constraints on the radius here. This agrees with the rules for
  message delivery as per the operational semantics of the network calculus, in which an
  arbitrary radius may be chosen for message delivery in order to model arbitrary variations
  in coverage.*)
  Qed.

(* If a message <m, l0> was sent t time units ago by some entity, then the distance
between l0 and the position of that entity is at most Smax*t.*)
Theorem sent_pos_bound (n : Network) (m : Mode) (t : Time) (i : nat)
  (l l0 : Position) (p : reachableProtNet n) :
  sent [baseMode m, basePosition l0] t i n p -> inPosNet l i n ->
  dist2d l l0 <= speedMax*t.
  (**Proof: By induction on the proof of sent.*)
  intros. generalize dependent l. induction H; intros.
  rename H3 into QQ. rename H2 into H3. rename H1 into H2. rename H0 into H1.
  rename QQ into H0. swapRename l l1.
  (*The base case would give us that the network n is reachable. From this we could
  deduce from an important general result (...reachableProt_triple...) that the software
  component of the entity i is P1 | P2 | P3.*)
  addHyp (reachable_net_prot n i q l1 h k p H). apply reachableProt_triple in H4.
  simpl in H4. invertClear H4. symmetry in H8.
  (*We could then show via another general result [salvaged?] that one of the sub-components
  must have been responsible for the output of v on the outProc channel.*)
  rewrite H8 in H2.
  assert (inPosNet l i n) as Q. erewrite inPos_pres_disc. apply H0. apply w.
  link_partripdiscex_tac2 p1' p2' p3'. link_partripout_tac Y.
  (*Using (...listener_outProc_out_not ...) we eliminate the listener case.*)
  Focus 3. lets LO : listener_outProc_out_not H7 Y. false.
  (*Now, for the broadcast case, we can infer further information with (bc_outProc_out)*)
  lets BO : bc_outProc_out Y H5.
  (*We then show by (bcReady_pos) that the position output is equal to the position of the sender.*)
  remember ([|q, l1, h, k|]) as e. assert (reachableProtEnt e). eapply reachable_net_ent.
  apply p. apply H. assert (bcReadyStateEnt m l0 e). rewrite Heqe. constructor.
  rewrite H8. constructor. apply BO. lets BP : bcReady_pos H4 H9.
  (*Then the goal is reduced to: |l - l| <= Smax*0 == 0 <= 0... which is trivial.*)
  eapply inPos_ent_net in BP. assert (l0 = l). eapply inPos_unique. apply BP.
  apply Q. rewrite H10. rewrite dist2D_refl. simpl. rewrite Rmult_0_r. apply Rle_refl.
  assumption.
  (*We use an analogous argument for the overlap case using (ovlp_outProc_out)*)
  lets OO : ovlp_outProc_out Y H6. destruct OO as [u [OO' _]].
  remember ([|q, l1, h, k|]) as e. assert (reachableProtEnt e). eapply reachable_net_ent.
  apply p. apply H. assert (ovReadyStateExpEnt m u l0 e).
  rewrite Heqe. constructor. rewrite H8. constructor. apply OO'.
  lets OP : ovReady_pos H4 H9. eapply inPos_ent_net in OP.
  assert (l0 = l). eapply inPos_unique. apply OP. apply Q. rewrite H10.
  rewrite dist2D_refl. simpl. rewrite Rmult_0_r. apply Rle_refl. assumption.
  (*The inductive cases follow immediately from the definition of sent and the semantics.*)
  (*Either a discrete action happens, in which case both t and the position of entity i don't change,
  and so the goal carries over directly from the previous case.*)
  assert (inPosNet l i n) as Q. erewrite inPos_pres_disc. apply H0. apply w.
  apply IHsent. assumption.
  (*Alternatively, a delay happens, in which case the new position l' of entity i differs from its
  old position by at most Smax*d [salvage].*)
  addHyp (inPos_del_bound_bkwd n n' d l i H0 w). invertClear H1. rename x into l1.
  invertClear H2. apply IHsent in H1. clear IHsent. rewrite distSymmetric in H3.
  (*And so by the (triangle inequality) the difference between l' and the sent position l0
  is at most Smax*t + Smax*d = Smax*(t + d), which is exactly the goal because the time
  parameter of sent for the current state is (t + d).*)
  addHyp (dist_tri_ineq l l1 l0). eapply Rle_trans. apply H2. simpl. rewrite Rmult_plus_distr_l.
  rewrite Rplus_comm. simpl in H1, H3. apply Rplus_le_compat; assumption. Qed.

(* If an entity is nextSince m for t time units and t is greater than the message latency,
then for some l0 it has delivered a message <m, l0> to some r at t - mL time units ago,
and the l0 in the message differs from the current position by at most Smax*t.*)
Theorem fst_delivered (n : Network) (m : Mode) (t : Time) (i : nat)
  (l : Position) (p : reachableProtNet n) :
  nextSince m t i n p -> inPosNet l i n -> forall q : msgLatency < t,
  exists l0 l1 r,
  delivered ([-[baseMode m, basePosition l0], l1, r-])
  (minusTime t msgLatency (Rlt_le msgLatency t q)) i n p /\
  dist2d l l0 <= speedMax*t.
  (*Proof: We call on (fst_sent) to achieve sent <m, l0> r t i n p.*)
  introz U. lets FS : fst_sent U. invertClearAs2 FS l0 SEN.
  (*Now we use (sent_pos_bound) to get that |l - l0| <= Smax*t.*)
  lets SPB : sent_pos_bound SEN U0.
  (*Now we use sent_delivered to show that the sent message was delivered.*)
  lets SD : sent_delivered SEN U1. ex_flat.
  (*Now we fill in the existentials.*)
  exists l0 x0 x.
  (*The rest follows from assumptions.*)
  split; assumption. Qed.
