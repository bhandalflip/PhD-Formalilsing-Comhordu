(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)


(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lib.GenTacs.
Require ComhCoq.lib.Extras.LibTactics.
From Stdlib Require Import Lra.

Section ProcEquiv.
Context {PNames : ProcNames} {PDefs : ProcDefs} {PGuarded : GuardedDefs}.

(********************** Bisimulation **********************)

(** Single step equivlance on process terms is defined as a bisimulation.*)
CoInductive bisimulation p q : Prop :=
  bisimWitness :
  (forall a p', p -P- a -P> p' ->
  exists q', q -P- a -P> q' /\ bisimulation p' q') ->
  (forall a q', q -P- a -P> q' ->
  exists p', p -P- a -P> p' /\ bisimulation p' q') ->
  bisimulation p q.
Notation "p ~p~ q" := (bisimulation p q) (at level 70).

(*** Generic Properties of the Relation ***)

(** The siumlation relation is reflexive.*)
CoFixpoint bisim_refl p : p ~p~ p. constructor.
  intros. exists p'. split. assumption. apply bisim_refl.
  intros. exists q'. split. assumption. apply bisim_refl. Qed.

(** The siumlation relation is transitive.*)
CoFixpoint bisim_trans p1 p2 p3 : p1 ~p~ p2 -> p2 ~p~ p3 ->
  p1 ~p~ p3. introz U. constructor.
  intros a p'. introz U. apply U in U1. ex_flat. and_flat.
  apply U0 in AND. ex_flat. and_flat. exists x0. split.
  assumption. eapply bisim_trans; eassumption.
  intros a q'. introz U. apply U0 in U1. ex_flat. and_flat.
  apply U in AND. ex_flat. and_flat. exists x0. split.
  assumption. eapply bisim_trans; eassumption. Qed.

CoFixpoint bisim_symm p q : p ~p~ q -> q ~p~ p.
  intros. inversion H. constructor.
  intros. apply H1 in H2. ex_flat. and_flat.
  apply bisim_symm in AND0. exists x. split; assumption.
  intros. apply H0 in H2. ex_flat. and_flat.
  apply bisim_symm in AND0. exists x. split; assumption.
  Qed.

(** A relation whose pairs match each other's steps, into pairs of the relation again, is
contained in bisimilarity.*)
Lemma bisim_coind (R : ProcTerm -> ProcTerm -> Prop) :
  (forall p q, R p q ->
    (forall a p', p -P- a -P> p' -> exists q', q -P- a -P> q' /\ R p' q') /\
    (forall a q', q -P- a -P> q' -> exists p', p -P- a -P> p' /\ R p' q')) ->
  forall p q, R p q -> p ~p~ q.
Proof.
  intro H. cofix CIH. intros p q Rpq. destruct (H p q Rpq) as [F B]. constructor.
  - intros a p' S. destruct (F a p' S) as [q' [S' R']]. exists q'. split; [exact S' | ].
    apply CIH. exact R'.
  - intros a q' S. destruct (B a q' S) as [p' [S' R']]. exists p'. split; [exact S' | ].
    apply CIH. exact R'.
Qed.

(*** Matching Steps ***)

(** One side of a bisimulation matches a discrete step of the other, with bisimilar
derivatives.*)
Lemma bisim_step_disc p q a p' : p ~p~ q -> p -PA- a -PA> p' ->
  exists q', q -PA- a -PA> q' /\ p' ~p~ q'.
Proof.
  intros B TR. inversion B as [F _].
  destruct (F _ _ (stepPDisc _ _ _ TR)) as [q' [TQ BQ]].
  exists q'. split; [ | exact BQ]. inversion TQ; subst; assumption.
Qed.

(** One side of a bisimulation matches a delay of the other, with bisimilar
derivatives.*)
Lemma bisim_step_del p q d p' : p ~p~ q -> p -PD- d -PD> p' ->
  exists q', q -PD- d -PD> q' /\ p' ~p~ q'.
Proof.
  intros B TR. inversion B as [F _].
  destruct (F _ _ (stepPTimed _ _ _ TR)) as [q' [TQ BQ]].
  exists q'. split; [ | exact BQ]. inversion TQ; subst; assumption.
Qed.

(** If one side of a bisimulation can do a discrete action, so can the other.*)
Lemma bisim_disc_match p p' q a : p ~p~ q -> p -PA- a -PA> p' ->
  exists q', q -PA- a -PA> q'.
Proof.
  intros B TR. destruct (bisim_step_disc _ _ _ _ B TR) as [q' [TQ _]]. eauto.
Qed.

(** Bisimilarity to a process that delays only to itself survives delays.*)
Lemma bisim_del_pres p p' X d : (forall d' q, X -PD- d' -PD> q -> q = X) ->
  p ~p~ X -> p -PD- d -PD> p' -> p' ~p~ X.
Proof.
  intros S B TR. destruct (bisim_step_del _ _ _ _ B TR) as [q [TQ BQ]].
  apply S in TQ. subst. exact BQ.
Qed.

(*** Unfolding and Prefixes ***)

(** A name applied to arguments is bisimilar to its unfolding.*)
Lemma app_bisim n l : n $( l )$ ~p~ unfoldApp n l.
Proof.
  rewrite unfoldApp_body. constructor.
  - intros a p' H. exists p'. split; [ | apply bisim_refl].
    inversion H; subst.
    + apply stepPDisc.
      match goal with [V : stepDiscProc (app n l) _ _ |- _] =>
        inversion V; subst end.
      match goal with [E : def n = _ |- _] => rewrite E end. assumption.
    + apply stepPTimed.
      match goal with [V : stepTimedProc (app n l) _ _ |- _] =>
        inversion V; subst end.
      match goal with [E : def n = _ |- _] => rewrite E end. assumption.
  - intros a q' H. exists q'. split; [ | apply bisim_refl].
    inversion H; subst.
    + apply stepPDisc. eapply stepDpApp; [apply surjective_pairing | eassumption].
    + apply stepPTimed. eapply stepTpApp; [apply surjective_pairing | eassumption].
Qed.

(** A name applied to arguments is bisimilar to the body of its definition, with the
arguments substituted for the parameters.*)
Lemma app_bisim_def n vs body l : def n = (vs, body) ->
  n $( l )$ ~p~ subProcTerm (listsToSub vs l) body.
Proof.
  intro D. eapply bisim_trans; [apply app_bisim | ].
  unfold unfoldApp. rewrite D. apply bisim_refl.
Qed.

(** A name without parameters is bisimilar to the body of its definition.*)
Lemma app_bisim_nil n body : def n = ([], body) -> n $( [] )$ ~p~ body.
Proof.
  intro D. eapply bisim_trans; [apply (app_bisim_def n [] body [] D) | ].
  simpl. rewrite subProc_id_eq. apply bisim_refl.
Qed.

(** Bisimilarity is a congruence for the output prefix.*)
Lemma outPrefix_bisim_context c l p q : p ~p~ q -> c $< l >$ ! p ~p~ c $< l >$ ! q.
Proof.
  revert p q. cofix CIH. intros p q B. constructor.
  - intros a p1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. exists q. split; [ | exact B].
      apply stepPDisc. constructor. assumption.
    + inversion S0; subst. exists (c $< l >$ ! q). split.
      * apply stepPTimed. constructor.
      * apply CIH. exact B.
  - intros a q1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. exists p. split; [ | exact B].
      apply stepPDisc. constructor. assumption.
    + inversion S0; subst. exists (c $< l >$ ! p). split.
      * apply stepPTimed. constructor.
      * apply CIH. exact B.
Qed.

(** Bisimilarity is a congruence for the input prefix, when the bodies are bisimilar for
every input.*)
Lemma inPrefix_bisim_context c xs p q :
  (forall v, typedVals xs v ->
    subProcTerm (listsToSub xs (listBaselistExp v)) p ~p~
    subProcTerm (listsToSub xs (listBaselistExp v)) q) ->
  c $< xs >$ ? p ~p~ c $< xs >$ ? q.
Proof.
  revert p q. cofix CIH. intros p q B. constructor.
  - intros a p1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. eexists. split.
      * apply stepPDisc. constructor. eassumption.
      * apply B. assumption.
    + inversion S0; subst. exists (c $< xs >$ ? q). split.
      * apply stepPTimed. constructor.
      * apply CIH. exact B.
  - intros a q1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. eexists. split.
      * apply stepPDisc. constructor. eassumption.
      * apply B. assumption.
    + inversion S0; subst. exists (c $< xs >$ ? p). split.
      * apply stepPTimed. constructor.
      * apply CIH. exact B.
Qed.

(** Bisimilarity is a congruence for the delay guard.*)
Lemma del_bisim_context e p q : p ~p~ q -> $< e >$ p ~p~ $< e >$ q.
Proof.
  revert e p q. cofix CIH. intros e p q B.
  destruct B as [B1 B2]. constructor.
  - intros a p1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst.
      match goal with H : p -PA- _ -PA> _ |- _ =>
        apply stepPDisc in H; apply B1 in H; destruct H as [q' [Sq Bq]] end.
      inversion Sq; subst.
      exists q'. split; [ | exact Bq].
      apply stepPDisc. apply stepDpTimeOut; assumption.
    + inversion S0; subst.
      * match goal with H : p -PD- _ -PD> _ |- _ =>
          apply stepPTimed in H; apply B1 in H; destruct H as [q' [Sq Bq]] end.
        inversion Sq; subst.
        exists q'. split; [ | exact Bq].
        apply stepPTimed. apply stepTpDelAdd; assumption.
      * eexists. split.
        -- apply stepPTimed. eapply stepTpDelSub. eassumption.
        -- apply CIH. constructor; assumption.
      * exists ($< e >$ q). split.
        -- apply stepPTimed. apply stepTpDelIll. assumption.
        -- apply CIH. constructor; assumption.
  - intros a q1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst.
      match goal with H : q -PA- _ -PA> _ |- _ =>
        apply stepPDisc in H; apply B2 in H; destruct H as [p' [Sp Bp]] end.
      inversion Sp; subst.
      exists p'. split; [ | exact Bp].
      apply stepPDisc. apply stepDpTimeOut; assumption.
    + inversion S0; subst.
      * match goal with H : q -PD- _ -PD> _ |- _ =>
          apply stepPTimed in H; apply B2 in H; destruct H as [p' [Sp Bp]] end.
        inversion Sp; subst.
        exists p'. split; [ | exact Bp].
        apply stepPTimed. apply stepTpDelAdd; assumption.
      * eexists. split.
        -- apply stepPTimed. eapply stepTpDelSub. eassumption.
        -- apply CIH. constructor; assumption.
      * exists ($< e >$ p). split.
        -- apply stepPTimed. apply stepTpDelIll. assumption.
        -- apply CIH. constructor; assumption.
Qed.

(** A delay guard matters only through its value.*)
Lemma del_bisim_guard e1 e2 p : evalExpFunTime e1 = evalExpFunTime e2 ->
  $< e1 >$ p ~p~ $< e2 >$ p.
Proof.
  revert e1 e2. cofix CIH. intros e1 e2 E. constructor.
  - intros a x S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. eexists. split; [ | apply bisim_refl].
      apply stepPDisc. apply stepDpTimeOut; [assumption | congruence].
    + inversion S0; subst.
      * eexists. split; [ | apply bisim_refl].
        apply stepPTimed. apply stepTpDelAdd; [assumption | congruence].
      * eexists. split; [ | apply bisim_refl].
        apply stepPTimed. apply stepTpDelSub. congruence.
      * exists ($< e2 >$ p). split.
        -- apply stepPTimed. apply stepTpDelIll. congruence.
        -- apply CIH. assumption.
  - intros a x S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. eexists. split; [ | apply bisim_refl].
      apply stepPDisc. apply stepDpTimeOut; [assumption | congruence].
    + inversion S0; subst.
      * eexists. split; [ | apply bisim_refl].
        apply stepPTimed. apply stepTpDelAdd; [assumption | congruence].
      * eexists. split; [ | apply bisim_refl].
        apply stepPTimed. apply stepTpDelSub. congruence.
      * exists ($< e1 >$ p). split.
        -- apply stepPTimed. apply stepTpDelIll. congruence.
        -- apply CIH. assumption.
Qed.

(** A delay guard that has run out does nothing.*)
Lemma del_zero_bisim e p : evalExpFunTime e = Some zeroTime -> $< e >$ p ~p~ p.
Proof.
  intro E. constructor.
  - intros a p1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. exists p1. split; [ | apply bisim_refl].
      apply stepPDisc. assumption.
    + inversion S0; subst.
      * match goal with [H : evalExpFunTime e = Some ?t |- _] =>
          rewrite E in H; injection H as H; subst t end.
        rewrite timeDelAddZeroL. exists p1. split; [ | apply bisim_refl].
        apply stepPTimed. assumption.
      * exfalso.
        match goal with [H : evalExpFunTime e = Some ?t |- _] =>
          rewrite E in H; injection H as H; subst t end.
        clear S S0. destruct d0 as [[dr dpos]]. simpl in *. lra.
      * congruence.
  - intros a q1 S. inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + exists q1. split; [ | apply bisim_refl]. apply stepPDisc.
      apply stepDpTimeOut; assumption.
    + exists q1. split; [ | apply bisim_refl]. apply stepPTimed.
      rewrite <- (timeDelAddZeroL d0). apply stepTpDelAdd; assumption.
Qed.

(** Delaying a timed guard whose body delays only to itself leaves the body under some
timer: what is left of the guard, or zero once it has run out.*)
Lemma del_del_bisim (e : Exp) (t : Time) (p q : ProcTerm) (d : Delay) :
  evalExpFunTime e = Some t ->
  (forall d' q', p -PD- d' -PD> q' -> q' = p) ->
  $< e >$ p -PD- d -PD> q -> exists (t' : Time), q ~p~ $< t' >$ p.
Proof.
  intros E S D. inversion D; subst.
  - match goal with [H : p -PD- _ -PD> q |- _] => apply S in H; subst q end.
    exists zeroTime. apply bisim_symm. apply del_zero_bisim. apply evalExpFunTime_time.
  - eexists. apply bisim_refl.
  - congruence.
Qed.

(*** Slightly more Specific ***)

(*TIDY*)

(*TOGO: GenTacs*)
Ltac plus_le_left_red := match goal with [Q : ?a + ?b = ?a + ?c |-
  ?b = ?c] => replace b with (a + b - a);[ | ring];
  rewrite Q; ring end.

Import ComhCoq.lib.Extras.LibTactics.
Open Scope R_scope.

(*TOGO: Wherever the sort shit is.*)

(** If a is in the sort relation for d, p, and p is capable of doing a delay
of d, then there is some d' < d and p' such that p can delay to this p' by
d' and the resulting p' is capable of doing the action a.*)
Lemma sort_del a d p : sort a d p -> timedActEnabled p d ->
  (exists p' d', p -PD- d' -PD> p' /\ d' < d /\ discActEnabled p' a)
  \/ discActEnabled p a.
  introz U. invertClearAs2 U0 p' PD.
  (*Induction on the delay rule.*)
  induction PD; inversion U; subst.
  (*Out pfx*)
  right; do 2 econstructor; assumption.
  (*In pfx*)
  right; do 2 econstructor. assumption.
  (*If true*)
  apply IHPD in H5. clear IHPD. invertClear H5. ex_flat. and_flat.
  invertClear AND2.
  left. repeat eexists; try eassumption. econstructor; eassumption.
  right. inversion H0. do 2 econstructor; eassumption.
  (*If false*)
  apply evalBoolExpTrueTot in H4. rewrite H in H4. inversion H4.
  (*Sum left*)
  apply IHPD1 in H2. clear IHPD1 IHPD2.
  invertClear H2; ex_flat; and_flat. left.
  assert (timedActEnabled p2 x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD2. assumption. invertClearAs2 TAE q' TP.
  do 2 eexists; try eassumption. split; [ | split; [eassumption | ]].
  econstructor; eassumption. apply daeSumL; assumption.
  right. apply daeSumL; assumption.
  (*Sum right*)
  apply IHPD2 in H2. clear IHPD1 IHPD2.
  invertClear H2; ex_flat; and_flat. left.
  assert (timedActEnabled p1 x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD1. assumption. invertClearAs2 TAE q' TP.
  do 2 eexists; try eassumption. split; [ | split; [eassumption | ]].
  econstructor; eassumption. apply daeSumR; assumption.
  right. apply daeSumR; assumption.
  (*Par left*)
  apply IHPD1 in H3. clear IHPD1 IHPD2.
  invertClear H3; ex_flat; and_flat. left.
  assert (timedActEnabled q x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD2. assumption.
  invertClearAs2 TAE q0 TP. do 2 eexists; try eassumption.
  split; [ | split; [eassumption | ]]. econstructor; try eassumption.
  unfold not. intros. assert (x0 <= d) as XLE. apply Rlt_le. assumption.
  eapply H; eapply sortLe; eassumption.
  apply daeParL; assumption.
  right. apply daeParL; assumption. 
  (*Par right*)
  apply IHPD2 in H3. clear IHPD1 IHPD2.
  invertClear H3; ex_flat; and_flat. left.
  assert (timedActEnabled p x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD1. assumption.
  invertClearAs2 TAE q0 TP. do 2 eexists; try eassumption.
  split; [ | split; [eassumption | ]]. econstructor; try eassumption.
  unfold not. intros. assert (x0 <= d) as XLE. apply Rlt_le. assumption.
  eapply H; eapply sortLe; eassumption.
  apply daeParR; assumption.
  right. apply daeParR; assumption.
  (*App*)
  rewrite H in H4. invertClear H4; subst.
  apply IHPD in H5. clear IHPD. or_flat. ex_flat. and_flat.
  left. do 2 eexists. split. econstructor; eassumption.
  split; assumption. right. eapply daeApp; eassumption.
  (*Del pfx*)
  rewrite H in H4. invertClear H4. subst.
  assert (d0 = d). apply delayEqR.
  plus_le_left_red.
  clear H0. subst. apply IHPD in H5.
  or_flat. ex_flat. and_flat. left. exists x (t0 +dt+ x0).
  split. apply stepTpDelAdd; assumption. split.
  apply Rplus_le_lt_compat. apply Rle_refl. assumption.
  assumption.
  (*Is the time 0 or some non-zero time.*)
  lets TLZ : Rle_lt_or_eq_dec zeroTime (nonneg t0) (cond_nonneg t0).
  (*Sub-case: Positive time, then we must assert a delay.*)
  elim_intro TLZ TL TE. mkdel t0 TL d0. assert (d0 <= t0) as Q.
  rewrite Heqd0. apply Rle_refl. left. exists ($< minusTime t0 d0 Q >$ p).
  exists d0. split. constructor. assumption. split.
  simpl. eapply Rle_lt_trans. eassumption. Rplus_lt_tac.
  delPos. subst. apply daeTimeout. simpl.
  apply evalExp_evalExpFunTime. lets EB : evalBase zeroTime.
  my_applys_eq EB. repeat f_equal. apply timeEqR. simpl.
  ring. assumption.
  (*Sub-case: Zero time, then the action is available now.*)
  right. apply daeTimeout. my_applys_eq H. f_equal.
  apply timeEqR. inversion TE. rewrite H1. simpl. 
  symmetry. assumption. assumption.
  (*Some contradictions that were floating around...?*)
  rewrite H0 in H5. inversion H5. rewrite H2 in H.
  false. eapply Rle_not_lt. apply H. simpl. Rplus_lt_tac.
  delPos.
  rewrite H in H4. inversion H4. Qed.

(*-TOGO*)

Lemma bisim_dae p q a : p ~p~ q -> discActEnabled p a ->
  discActEnabled q a. introz U. invertClear U0.
  apply stepPDisc in H. apply U in H. ex_flat. and_flat.
  econstructor. inversion AND. eassumption. Qed.

(*-TIDY*)

Lemma bisim_del_sort p q a d : p ~p~ q -> timedActEnabled p d ->
  sort a d p -> sort a d q. introz U.
  lets SD : sort_del U1 U0. elim_intro SD PD DA.
  ex_flat. and_flat. apply stepPTimed in AND. apply U in AND.
  ex_flat. and_flat. invertClear AND.
  lets DAX : bisim_dae AND0 AND2.
  apply sort_complete. split. eapply sortNotTau. eassumption.
  right. exists x0 x1. repeat (split; [assumption | ]).
  assumption.
  lets BD : bisim_dae U DA. apply enabledInSort. assumption.
  eapply sortNotTau. eassumption. Qed.

(*** Bisimulation and Syntax ***)

CoFixpoint choice_bisim_symm p1 p2 : p1 $+$ p2 ~p~ p2 $+$ p1. constructor.
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  exists p'. split. apply stepPDisc. apply stepDpChoiceR.
  assumption. apply bisim_refl.
  (*Right sub-case*)
  exists p'. split. apply stepPDisc. apply stepDpChoiceL.
  assumption. apply bisim_refl.
  (*Timed case*)
  inversion H0. exists (p2' $+$ p1'). split.
  apply stepPTimed. constructor; assumption.
  apply choice_bisim_symm .
  (*Repeat everything again for symmetric case*)
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  exists q'. split. apply stepPDisc. apply stepDpChoiceR.
  assumption. apply bisim_refl.
  (*Right sub-case*)
  exists q'. split. apply stepPDisc. apply stepDpChoiceL.
  assumption. apply bisim_refl.
  (*Timed case*)
  inversion H0. exists (p2' $+$ p1'). split.
  apply stepPTimed. constructor; assumption.
  apply choice_bisim_symm . Qed.

CoFixpoint par_bisim_symm p1 p2 : p1 $||$ p2 ~p~ p2 $||$ p1. constructor.
  intros. inversion H.
  (*Discrete case*)
  inversion H0; subst.
  (*Left sub-case*)
  exists (p2 $||$ p'0). split. apply stepPDisc. apply stepDpParR.
  assumption. apply par_bisim_symm.
  (*Right sub-case*)
  exists (q' $||$ p1). split. apply stepPDisc. apply stepDpParL.
  assumption. apply par_bisim_symm.
  (*Sync LR*)
  exists (q' $||$ p'0). split. apply stepPDisc. eapply stepDpSyncRL;
  eassumption. apply par_bisim_symm.
  (*Sync RL*)
  exists (q' $||$ p'0). split. apply stepPDisc. eapply stepDpSyncLR;
  eassumption. apply par_bisim_symm.
  (*Timed case*)
  inversion H0. exists (q' $||$ p'0). split.
  apply stepPTimed. constructor; try assumption.
  unfold not. intros. eapply H9. eassumption.
  my_applys_eq H10. symmetry. apply complementInvol.
  apply par_bisim_symm.
  (*Repeat everything again for symmetric case-
  with left and right reversed.*)
  intros. inversion H.
  (*Discrete case*)
  inversion H0; subst.
  (*Right sub-case*)
  exists (p1 $||$ p'). split. apply stepPDisc. apply stepDpParR.
  assumption. apply par_bisim_symm.
  (*Left sub-case*)
  exists (q'0 $||$ p2). split. apply stepPDisc. apply stepDpParL.
  assumption. apply par_bisim_symm.
  (*Sync LR*)
  exists (q'0 $||$ p'). split. apply stepPDisc. eapply stepDpSyncRL;
  eassumption. apply par_bisim_symm.
  (*Sync RL*)
  exists (q'0 $||$ p'). split. apply stepPDisc. eapply stepDpSyncLR;
  eassumption. apply par_bisim_symm.
  (*Timed case*)
  inversion H0. exists (q'0 $||$ p'). split.
  apply stepPTimed. constructor; try assumption.
  unfold not. intros. eapply H9. eassumption.
  my_applys_eq H10. symmetry. apply complementInvol.
  apply par_bisim_symm. Qed.

CoFixpoint choice_bism_unit_r p : p $+$ nilProc ~p~ p.
  constructor; intros; inversion H.
  (*Discrete case*)
  inversion H0; subst.
  (*Left sub-case*)
  apply stepPDisc in H7. exists p'. split.
  assumption. apply bisim_refl.
  (*Right sub-case*)
  inversion H7.
  (*Timed case*)
  inversion H0; inversion H8; subst.
  exists p1'. split. apply stepPTimed.
  assumption. apply choice_bism_unit_r.
  (*Right to left case is easy.*)
  (*Discrete case*)
  subst. exists q'. split. apply stepPDisc.
  eapply stepDpChoiceL. assumption. apply bisim_refl.
  (*Timed case*)
  subst. exists (q' $+$ nilProc). split. apply stepPTimed.
  eapply stepTpSum. assumption. constructor.
  apply choice_bism_unit_r. Qed.

CoFixpoint choice_bism_unit_l p : nilProc $+$ p ~p~ p.
  eapply bisim_trans. apply choice_bisim_symm.
  apply choice_bism_unit_r. Qed.

CoFixpoint choice_bisim_context p1 p2 p1' p2' :
  p1 ~p~ p1' -> p2 ~p~ p2' ->
  p1 $+$ p2 ~p~ p1' $+$ p2'. introz U. constructor.
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  apply stepPDisc in H7. apply U in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceL. assumption. assumption.
  (*Right sub-case*)
  apply stepPDisc in H7. apply U0 in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceR. assumption. assumption.
  (*Timed case*)
  inversion H0.
  apply stepPTimed in H5. apply stepPTimed in H8.
  apply U in H5. apply U0 in H8. ex_flat. and_flat.
  exists (x0 $+$ x). inversion AND. inversion AND1.
  split. apply stepPTimed. constructor; assumption.
  apply choice_bisim_context; assumption.
  (*Repeat everything again for symmetric case*)
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  apply stepPDisc in H7. apply U in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceL. assumption. assumption.
  (*Right sub-case*)
  apply stepPDisc in H7. apply U0 in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceR. assumption. assumption.
  (*Timed case*)
  inversion H0.
  apply stepPTimed in H5. apply stepPTimed in H8.
  apply U in H5. apply U0 in H8. ex_flat. and_flat.
  exists (x0 $+$ x). inversion AND. inversion AND1.
  split. apply stepPTimed. constructor; assumption.
  apply choice_bisim_context; assumption.
  Qed.

(*LOCAL TIDY*)

Ltac bisim_disc_tac_parm U V :=
  apply stepPDisc in V; apply U in V; ex_flat; and_flat;
  match goal with [U1 : _ -P- _ -P> _ |- _] => inversion U1; subst end.

(**If there are bisimilar processes in the context and there's a discrete
transition from the first bisimilar process then this tactic generates a
matching discrete transition from the second bisimilar process.*)
Ltac bisim_disc_tac :=
  match goal with
  | [U : ?p ~p~ ?q, V : ?p -PA- _ -PA> _ |- _] =>
    bisim_disc_tac_parm U V
  | [U : ?p ~p~ ?q, V : ?q -PA- _ -PA> _ |- _] =>
    bisim_disc_tac_parm U V
  end.

Ltac bisim_timed_tac_parm U V :=
  apply stepPTimed in V; apply U in V; ex_flat; and_flat;
  match goal with [U1 : _ -P- _ -P> _ |- _] => inversion U1; subst end.

(**Similar to bisim_disc_tac but matches a delay rather than a discrete step.*)
Ltac bisim_timed_tac :=
  match goal with
  | [U : ?p ~p~ ?q, V : ?p -PD- _ -PD> _ |- _] =>
    bisim_timed_tac_parm U V
  | [U : ?p ~p~ ?q, V : ?q -PD- _ -PD> _ |- _] =>
    bisim_timed_tac_parm U V
  end.

(*-LOCAL TIDY*)

Lemma cond_bisim_lift_true p q b : p ~p~ q -> evalBoolExp b true ->
  b $> p ~p~ b $> q. intros. constructor.
  intros. inversion H1.
  (*Disc case*)
  inversion H2.
  bisim_disc_tac. exists x. split. do 2 constructor;
  assumption. assumption.
  (*Timed case*)
  inversion H2. bisim_timed_tac. exists x. split.
  do 2 constructor; assumption. assumption.
  apply evalBoolExpTrueTot in H0. rewrite H0 in H9.
  inversion H9.
  (*Repeat everything. Ugh.*)
  intros. inversion H1.
  (*Disc case*)
  inversion H2.
  bisim_disc_tac. exists x. split. do 2 constructor;
  assumption. assumption.
  (*Timed case*)
  inversion H2. bisim_timed_tac. exists x. split.
  do 2 constructor; assumption. assumption.
  apply evalBoolExpTrueTot in H0. rewrite H0 in H9.
  inversion H9.
  Qed.

CoFixpoint par_bisim_context p p' q :
  p ~p~ p' -> p $||$ q ~p~ p' $||$ q.
  intros. constructor. 
  (*We discriminate the cases*)
  intros. invertClear H0; subst.
  (*First, the discrete case.*)
  invertClear H1; subst.
  (*Sub case: left component action*)
  bisim_disc_tac. exists (x $||$ q). split. apply stepPDisc.
  apply stepDpParL. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: right component action*)
  exists (p' $||$ q'). split. apply stepPDisc.
  apply stepDpParR. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: left to right synch*)
  bisim_disc_tac. exists (x $||$ q'). split. apply stepPDisc.
  eapply stepDpSyncLR; eassumption. apply par_bisim_context.
  assumption.
  (*Sub case: right to left synch*)
  bisim_disc_tac. exists (x $||$ q'). split. apply stepPDisc.
  eapply stepDpSyncRL; eassumption. apply par_bisim_context.
  assumption.
  (*Now the delay case. This is where we need to use that quirky,
  beautiful little result about sort.*)
  invertClear H1; subst. bisim_timed_tac.
  exists (x $||$ q'). split. do 2 constructor; [assumption.. | ].
  unfold not. intros. eapply H7. eapply bisim_del_sort.
  apply bisim_symm. eassumption. econstructor. eassumption.
  eassumption. assumption.
  apply par_bisim_context. assumption.
  (*Symmetric case*)
  (*We discriminate the cases*)
  intros. invertClear H0; subst.
  (*First, the discrete case.*)
  invertClear H1; subst.
  (*Sub case: left component action*)
  bisim_disc_tac. exists (x $||$ q). split. apply stepPDisc.
  apply stepDpParL. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: right component action*)
  exists (p $||$ q'0). split. apply stepPDisc.
  apply stepDpParR. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: left to right synch*)
  bisim_disc_tac. exists (x $||$ q'0). split. apply stepPDisc.
  eapply stepDpSyncLR; eassumption. apply par_bisim_context.
  assumption.
  (*Sub case: right to left synch*)
  bisim_disc_tac. exists (x $||$ q'0). split. apply stepPDisc.
  eapply stepDpSyncRL; eassumption. apply par_bisim_context.
  assumption.
  (*Now the delay case. This is where we need to use that quirky,
  beautiful little result about sort.*)
  invertClear H1; subst. bisim_timed_tac.
  exists (x $||$ q'0). split. do 2 constructor; [assumption.. | ].
  unfold not. intros. eapply H7. eapply bisim_del_sort.
  apply bisim_symm. apply bisim_symm in H. eassumption. econstructor.
  eassumption. eassumption. assumption.
  apply par_bisim_context. assumption.
  Qed.

Corollary par_bisim_context2 p q q' :
  q ~p~ q' -> p $||$ q ~p~ p $||$ q'. intros.
  eapply bisim_trans. apply par_bisim_symm.
  eapply bisim_trans. apply par_bisim_context.
  eassumption. apply par_bisim_symm. Qed.

Corollary par_bisim_context_strong p p' q q' :
  p ~p~ p' -> q ~p~ q' -> p $||$ q ~p~ p' $||$ q'.
  intros. eapply bisim_trans. apply par_bisim_context.
  eassumption. apply par_bisim_context2. assumption. Qed.

(** Bisimilarity is a congruence for the parallel composition of any number of processes.*)
Lemma parAll_bisim_context p ps p' ps' :
  Forall2 bisimulation (p :: ps) (p' :: ps') -> parAll p ps ~p~ parAll p' ps'.
Proof.
  revert p p' ps'. induction ps as [ |q qs IH]; intros p p' ps' F;
    inversion F as [ | ? ? ? ? B F']; subst; inversion F'; subst; simpl.
  - assumption.
  - apply par_bisim_context_strong; [assumption | ]. apply IH. assumption.
Qed.

Lemma cond_bisim_true p b : evalBoolExp b true ->
  b $> p ~p~ p. introz U.
  split; intros. exists p'. split;[ | apply bisim_refl].
  inversion H; inversion H0. apply stepPDisc. assumption.
  apply stepPTimed. assumption. apply evalBoolExpTrueTot in U.
  rewrite U in H7. inversion H7.
  (*Other direction*)
  inversion H. exists q'. split;[ | apply bisim_refl]. 
  do 2 constructor. assumption. apply evalBoolExpTrueTot.
  assumption. exists q'. split;[ | apply bisim_refl].
  do 2 constructor. assumption. apply evalBoolExpTrueTot.
  assumption. Qed.

(*TOGO: LanguageFoundations*)

(** Only this direction holds: the total function also returns false when the expression
does not evaluate at all.*)
Theorem evalBoolExpFalseTot : forall (e : BoolExp),
  evalBoolExp e false -> evalBoolExpFunTot e = false.
Proof using.
  intros e H. apply evalBoolExpRelFun in H.
  unfold evalBoolExpFunTot. rewrite H. reflexivity.
Qed.
  

(*TOGO*)

CoFixpoint cond_bisim_false p b : evalBoolExpFunTot b = false ->
  b $> p ~p~ nilProc. introz U. split; intros. 
  inversion H; inversion H0.
  apply evalBoolExpTrueTot in H8.
  apply evalBoolExpTrueTot in H8. rewrite U in H8.
  inversion H8. rewrite U in H8. inversion H8.
  subst. exists nilProc. split. do 2 constructor.
  apply cond_bisim_false; assumption.
  inversion H; inversion H0; subst.
  exists (b $> p). split. constructor.
  apply stepTpIfFalse; assumption. apply cond_bisim_false.
  assumption. Qed.

Lemma if_then_bisim_true b p q :
  evalBoolExp b true -> b $> p $+$ !~b $> q ~p~ p.
  introz U. cut (!~b $> q ~p~ nilProc). intro NP.
  eapply bisim_trans. eapply choice_bisim_context.
  apply bisim_refl. apply NP. eapply bisim_trans.
  apply choice_bism_unit_r. apply cond_bisim_true.
  assumption. apply cond_bisim_false.
  unfold evalBoolExpFunTot. simpl.
  apply evalBoolExpRelFun in U. rewrite U.
  simpl. reflexivity. Qed.

Lemma if_then_bisim_false b p q :
  evalBoolExp b false -> b $> p $+$ !~b $> q ~p~ q.
  introz U. cut (b $> p ~p~ nilProc). intro NP.
  eapply bisim_trans. eapply choice_bisim_context.
  apply NP. apply bisim_refl. eapply bisim_trans.
  apply choice_bism_unit_l. apply cond_bisim_true.
  apply bevalNot in U. apply U.
  apply cond_bisim_false. apply evalBoolExpRelFun in U.
  unfold evalBoolExpFunTot. rewrite U. simpl.
  reflexivity. Qed.

(** When the condition is ill formed, neither branch is available.*)
Lemma if_then_bisim_none b p q :
  evalBoolExpFun b = None -> b $> p $+$ !~ b $> q ~p~ nilProc.
Proof.
  intro E. eapply bisim_trans.
  { apply choice_bisim_context; apply cond_bisim_false;
      unfold evalBoolExpFunTot; simpl; rewrite E; reflexivity. }
  apply choice_bism_unit_r.
Qed.

End ProcEquiv.

(** A section's notations and tactics end with it. So that later files can use them, the
notations are declared again here.*)
Notation "p ~p~ q" := (bisimulation p q) (at level 70).
