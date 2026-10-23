(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** In this file is the main result. We could also include any other results of interest here
if time allowed it.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Reals Arith.
Require Import ComhCoq.lib.Extras.LibTactics.
Require Import ComhCoq.lib.GenTacs.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.lang.NetworkLanguage.
(*Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.EntAux.*)
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.NARNonFS_currSince.
Require Import ComhCoq.protocol.NARMisc.
Require Import ComhCoq.protocol.NARIncomp.
Require Import ComhCoq.protocol.NARTop.
Require Import ComhCoq.protocol.ProtocolBridge.

Section Main.
Context {Model : ComhModel}.

(**Used to exploit a symmetry in the following proof, essentially continues on the proof
from where it is applied*)
Local Theorem safety_aux (n : Network) (X : reachableProtNet n) (e1 e2 : Entity)
  (i j : nat) (H : (i <> j)%nat) (H0 : e1 @ i .: n) (H1 : e2 @ j .: n)
  (x : Distance) (Heqx : x = mkDistance (dist2d e1 e2)) (mdc : Distance) (m1 : Mode)
  (Heqm1 : m1 = e1) (m2 : Mode) (Heqm2 : m2 = e2) (Heqmdc : mdc = minDistComp m1 m2)
  (H2 : x < mdc) (H3 : ~ failSafe m1) (H4 : ~ failSafe m2) (H5 : currModeNet m1 i n)
  (H6 : currModeNet m2 j n) (t1 : Time) (H7 : currSince m1 t1 i n X) (t2 : Time)
  (H8 : currSince m2 t2 j n X) (H9 : msgLatency + Rmax adaptNotif transMax < t1)
  (H10 : msgLatency + Rmax adaptNotif transMax < t2) (H11 : t1 <= t2) : False.
Proof.
  (*Now, let's focus on the entity e1. We know that currSince m1 t1 e1 implies that a
  message of the form <m1, l'> was delivered t time units ago to a sufficient radius 
  (for m1) r by e1, where t is in the interval Ipd m1 (a) and t < t1 (b) and the distance
  between l1 and l' is at most Smax*(mL + t) (bb) (NA::pre-del-suff). Since we have
  that t1 <= t2 we can infer by transitivity t < t2 (c).*)
  addHyp (inPos_ex i n e1 H0). invertClear H12. rename x0 into l1.
  addHyp (pre_del_suff n m1 t1 i l1 X H7 H13 H3). decompose [ex] H12. clear H12.
  rename x0 into t. rename x1 into r. rename x2 into l'. rename x3 into l''.
  decompose [and] H15. clear H15. assert (t < t2). eapply Rlt_le_trans.
  apply H17. assumption.
  (*Now, we know from the definition of Ipd that:
	t <= max AN trans + period m1 + trans m1
	=> 2*Smax*t <= 2*Smax*(max AN trans + period m1 + trans m1) (a)
  But we also know from (0) that
	x < mdc m1 m2 (b)
  Adding the inequalities (a) and (b) we get
	x + 2*Smax*t < mdc m1 m2 + 2*Smax*(max AN trans + period m1 + trans m1)
  Also, we know from (5) that r is sufficient for the mode m1, which expands to:
	maxMinDistComp m1 + 2*Smax*(max AN trans + period m1 + trans m1) <= r.
  Since mdc m1 m2 <= maxMinDistComp m1 by definition, then we can infer from a bit of
  transitivity that
	x + 2*Smax*t < r. Which can be weakened to x + 2*Smax*t <= r.*)
  inversion H14. addHyp (Rmult_le_compat_l (2*speedMax) t
  (upper (preDeliveredInterval m1)) speedMax_double_nonneg H20).
  addHyp (Rplus_lt_le_compat x mdc (2 * speedMax * t)
  (2 * speedMax * upper (preDeliveredInterval m1)) H2 H21).
  unfold sufficient in H16. addHyp (maxMinDistCompBound m1 m2).
  rewrite <- Heqmdc in H23. assert (x + 2*speedMax*t < r).
  eapply Rlt_le_trans. apply H22. eapply Rle_trans;[ |apply H16].
  simpl. eapply Rplus_le_compat. assumption. apply Rle_refl.
  (*We can now show that e2 received the message <m1, l'> t time units ago by the
  delivery result of (5), the inequality x + 2*Smax*t <= r of (6) and the result
  (delivered-received). Picture:
  <m1, l'>_r!---------|-t-|---------------e1 (delivered by e1, r sufficient)
  <m1, l'>?---------|-t-|---------------e2 (received by e2)*)
  apply Rlt_le in H24. addHyp (delivered_received n ([baseMode m1, basePosition l'])
  t r x i j X l'' H12 H (distNet_intro e1 e2 i j n x H0 H1 Heqx) H24).
  (*By H19, we know that the distance between l1 and l' is at most Smax*(mL + t).
  And so we have by the (triangle inequality) that:
	|l2 - l'| <= x + Smax*(mL + t)
  Since x < mdc m1 m2 (0), then we can deduce:
	|l2 - l'| < mdc m1 m2 + Smax*mL + Smax*t
  Rearranging:
	|l2 - l'| - Smax*mL < mdc m1 m2 + Smax*t
  Adding Smax*t to both sides:
	|l2 - l'| - Smax*mL + Smax*t < mdc m1 m2 + 2*Smax*t
  Reusing the result at 6 (a):
	2*Smax*t <= 2*Smax*(max AN trans + period m1 + trans m1)
  and so
	|l2 - l'| - Smax*mL + Smax*t <
        mdc m1 m2 + 2*Smax*(max AN trans + period m1 + trans m1)
  But the right hand side of this is just Dpi m1 m2. Tidying up then:
	|l2 - l'| - Smax*mL + Smax*t < Dpi m1 m2.*)
  addHyp (inPos_ex j n e2 H1). invertClear H26. rename x0 into l2.
  addHyp (inPos_pos e1 i l1 n H0 H13). addHyp (inPos_pos e2 j l2 n H1 H27).
  rewrite H26, H28 in Heqx. addHyp (dist_tri_ineq l2 l1 l').
  assert ((distance x) = dist2d l2 l1). rewrite distSymmetric. 
  rewrite Heqx. reflexivity. rewrite <- H30 in H29.
  assert (nonneg (dist2d l2 l') <= nonneg (distance x) +
  nonneg speedMax * (nonneg (time msgLatency) + nonneg (time t))).
  eapply Rle_trans. apply H29. apply Rplus_le_compat. apply Rle_refl.
  assumption.
  replace (nonneg speedMax * (nonneg (time msgLatency) + nonneg (time t))) with
  (nonneg speedMax * nonneg (time msgLatency) + nonneg speedMax * nonneg (time t))
  in H31;[ | ring]. assert (nonneg (distance x) +
  (nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t)) < mdc +
  (nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t))). apply Rplus_lt_le_compat.
  assumption. apply Rle_refl. assert (dist2d l2 l' < mdc +
  (nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t))). eapply Rle_lt_trans. apply H31.
  assumption. replace (nonneg (distance mdc) +
  (nonneg speedMax * nonneg (time msgLatency) + nonneg speedMax * nonneg (time t)))
  with (nonneg speedMax * nonneg (time msgLatency) + (nonneg (distance mdc) + 
  nonneg speedMax * nonneg (time t))) in H33;[ | ring].
  apply Rplus_lt_swap_rl in H33.
  apply (Rplus_lt_compat_r (speedMax*t)) in H33.
  replace (mdc + nonneg speedMax * nonneg (time t) + nonneg speedMax * nonneg (time t)) with
  (mdc + 2*nonneg speedMax * nonneg (time t)) in H33; [ | ring].
  assert (nonneg (dist2d l2 l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t) <
  nonneg (distance mdc) + 2 * nonneg speedMax * upper (preDeliveredInterval m1)).  
  eapply Rlt_le_trans. apply H33. apply Rplus_le_compat. apply Rle_refl.
  assumption. rewrite Heqmdc in H34. remember (dist2d l2 l') as q0. simpl in H34.
  rewrite minDistCompSymmetric in H34.
  fold (possIncDist m2 m1) in H34. rewrite Heqq0 in H34.
  (*Now, 5 (a) states that t is in Ipd, and therefore 0 < t. Applying the result
  (incomp_tfs) to this and to (2) (7) (5-c) (8) we can show that e2 is tfs m t'', t <= t''.
  And so by (tfs-bound), t <= t'' <= trans m <= trans. But by 5 (a) we have that t is
  in the Ipd of m1 and so max AN trans < t, so trans < t. But t <= trans. Hence we have
  a contradiction and can reject the hypothesis, namely that there was an unsafe reachable
  state, concluding that all such states are, to the contrary, safe.*)
  assert (zeroTime < t). simpl in H18. eapply Rle_lt_trans;[ |apply H18].
  eapply Rle_trans;[ |apply Rmax_l]. timeNonneg.  
  assert ((speedMax * t) < possIncDist m2 m1). eapply Rle_lt_trans.
  apply Rmult_le_compat_l. apply cond_nonneg. apply H20.
  unfold possIncDist. simpl. apply Rplus_lt_weaken_rl. apply cond_nonneg.
  rewrite Rmult_assoc. rewrite double. apply Rlt_double.
  apply Rmult_lt_0. apply speedMax_pos. apply Rlt_le_zero_plus. apply Rlt_le_zero_plus.
  apply Rmax_lt_l. apply adaptNotif_positive. apply cond_nonneg.
  apply cond_nonneg.
  (*We now just switch over to the -nn- version of subtraction, which our expression
  language, and hence our little computing entities, deals with.*)
  lets RPL : Rminus_plus_lt_subNonnegTot H36.
  rewrite <- multNonneg_Rmult_eq in H34. apply RPL in H34. clear H36.
  destruct (incomp_tfs n t2 t l2 l' j m2 m1 X H4 H8 H27 H25 H35 H15 H34) as [t'' [LE TF]].
  apply tfs_bound in TF. simpl in H18. assert (transMax < t).
  eapply Rle_lt_trans;[ |apply H18]. apply Rmax_r.
  eapply Rlt_not_le. apply H36. eapply Rle_trans. apply LE. eapply Rle_trans. apply TF.
  apply transMaxBound.
Qed.

(**This is the main result stating the correctness of the protocol. It says that if a network
is reachable, then it is safe. To recap, what this means is that, if we start out a system in
which all the entities are fail safe and running the protocol process as their software
component, and we allow this system to evolve via any finite number of delays and discrete
actions as per our transition semantics, then we end up with a network which is safe. Safety
itself is defined elsewhere, but basically means that all pairs of entities in the network are
separated by a sufficient distance to ensure that they are not incompatible according to their
respective modes. The sufficiency of the distance in question is in turn decided by parameters
of the specific system in question. The result holds for every choice of those parameters
that meets the assumptions of the model, [ComhModel].*)
Theorem safety (n : Network) : reachableProtNet n -> safe n.
Proof.
  (*So our assumption is that there exists some initial reachable network in which there is
  some pair of entities that are separated by a distance less than the minimum distance
  of compatibility for their respective modes. Let's call the entities e1 and e2 and
  modes m1 and m2 respectively. Let x be the distance between the two entities.
  Then our assumption says x < mdc m1 m2. Let e1 = [P1, l1, I1, K1] and
  e2 = [P1, l1, I1, K1]- this is simply the decomposition of each entity into its
  constituent parts (zooming in if you like).
  e1[m1]-------------|-x-|---------------e2[m2]
  (e1 in m1 and e2 in m2 separated by distance x)*)
  unfold safe. intros. addHyp (dec_compatible e1 e2). appDisj H2.
  unfold compatible in H2. remember (dist2d e1 e2) as x.
  apply not_Rle_lt in H2. remember (minDistComp e1 e2) as mdc.
  remember (currModeEnt e1) as m1. remember (currModeEnt e2) as m2. apply False_ind.
  (*We know that both m1 and m2 are non-fail-safe modes because otherwise the
  minimum distance of compatibility would be 0 (by an axiom), and we'd have x < 0,
  which contradicts the non-negativity of distance.*)
  assert (~failSafe m1). addHyp (fsDecMode m1). appDisj H3.
  addHyp (minDistCompFS m1 m2 H3). rewrite H4 in Heqmdc. rewrite Heqmdc in H2.
  simpl in H2. 
  nonneg_lt0_contra.
  assert (~failSafe m2). addHyp (fsDecMode m2). appDisj H4.
  addHyp (minDistCompFS m2 m1 H4). rewrite minDistCompSymmetric in H5.
  rewrite H5 in Heqmdc. rewrite Heqmdc in H2. simpl in H2.
  nonneg_lt0_contra.
  (*Hence both e1 and e2 have been currSince m1 t1 and currSince m2 t2 respectively
  (NA::nonFS-currSince).*)
  addHyp (currMode_intro m1 e1 i n Heqm1 H0).
  addHyp (currMode_intro m2 e2 j n Heqm2 H1).
  addHyp (nonFS_currSince m1 i n X H5 H3). invertClear H7. rename x0 into t1.
  addHyp (nonFS_currSince m2 j n X H6 H4). invertClear H7. rename x0 into t2.
  (*It can further be shown that these values t1 and t2 are strictly bounded from
  below by mL + max(AN, trans) (NA::currSince-lower-bound).*)
  addHyp (currSince_lower_bound n t1 m1 i X H8).
  addHyp (currSince_lower_bound n t2 m2 j X H9).
  (*Without loss of generality, we can assume that t1 <= t2. A moment's pause
  for a picture now:
  (m2)-----------------|-t2-|---------------e2
      (m1)-------------|-t1-|---------------e1*)
  apply lt_notEq in H. addHyp (Rle_or_le t1 t2).
  remember (mkDistance x) as x'. swapRename x x'. rewrite Heqx in Heqx'.
  assert (x < mdc). rewrite Heqx'. rewrite <- Heqx. assumption.
  invertClear H11.
  eapply safety_aux;eassumption. apply notEq_symm in H.
  rewrite distSymmetric in Heqx'. rewrite minDistCompSymmetric in Heqmdc.
  eapply safety_aux;eassumption.
  (**Proof is then continued by the auxiliary result safety_aux*) Qed.

End Main.
