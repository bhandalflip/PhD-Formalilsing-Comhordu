(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.ProtocolBridge.

(***************************** Misc *****************************)

(** The software of a reachable entity is reachable from the protocol process.*)
Lemma reachable_ent_prot p l h k : reachableProtEnt ([| p, l, h, k |]) ->
  reachableProt p.
Proof.
  intro R. apply reachableProt_reachableFrom. exact (reachableEnt_proc _ _ R).
Qed.

(** An entity in a stable mode has no next mode.*)
Lemma nextModeEnt_not_stable m1 (m2 : Mode) p l h :
  nextModeEnt ([|p, l, h, m2|]) = Some m1 -> False.
Proof.
  intro H. simpl in H. discriminate.
Qed.

(***************************** Steps to a component *****************************)
(** The language takes an entity step down to the components of its software, for any
number of them (ent_disc_comps and its kin in EntityLanguage.v). Here the software is the
protocol's triple.*)

(** A discrete step between triples: each component is unchanged or stepped once.*)
Lemma triple_disc_ent p1 p2 p3 p1' p2' p3' l l' h h' k k' a :
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- a ->> [|p1' $||$ p2' $||$ p3', l', h', k'|] ->
  (p1 = p1' \/ exists b, p1 -PA- b -PA> p1') /\ (p2 = p2' \/ exists b, p2 -PA- b -PA> p2') /\
  (p3 = p3' \/ exists b, p3 -PA- b -PA> p3').
Proof.
  intro S. change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in S.
  change (p1' $||$ p2' $||$ p3') with (parAll p1' [p2', p3']) in S.
  lets F : ent_disc_comps S. specialize (F eq_refl). triple_pos. repeat split; assumption.
Qed.

(** A delay between triples: each component delays by it.*)
Lemma triple_del_ent p1 p2 p3 p1' p2' p3' l l' h h' k k' d :
  [|p1 $||$ p2 $||$ p3, l, h, k|] -ED- d ->> [|p1' $||$ p2' $||$ p3', l', h', k'|] ->
  p1 -PD- d -PD> p1' /\ p2 -PD- d -PD> p2' /\ p3 -PD- d -PD> p3'.
Proof.
  intro S. change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in S.
  change (p1' $||$ p2' $||$ p3') with (parAll p1' [p2', p3']) in S.
  lets F : ent_del_comps S. specialize (F eq_refl). triple_pos. repeat split; assumption.
Qed.

(** A discrete step from a triple leads to a triple, each component unchanged or stepped
once.*)
Lemma triple_disc_ent_fwd p1 p2 p3 l h k e' a :
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- a ->> e' ->
  exists p1' p2' p3' l' h' k', e' = [|p1' $||$ p2' $||$ p3', l', h', k'|] /\
  (p1 = p1' \/ exists b, p1 -PA- b -PA> p1') /\ (p2 = p2' \/ exists b, p2 -PA- b -PA> p2') /\
  (p3 = p3' \/ exists b, p3 -PA- b -PA> p3').
Proof.
  intro S. change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in S.
  destruct (ent_disc_comps_fwd _ _ _ _ _ _ _ S) as [p1' [qs' [l' [h' [k' [E F]]]]]].
  positions_inv. do 6 eexists. split; [reflexivity | ]. repeat split; assumption.
Qed.

(** Takes an entity state predicate H apart, for a predicate lifted from one component:
the entity becomes [|p1 $||$ p2 $||$ p3, l, h, k|] and H the component's predicate.*)
Ltac ent_state_destr H p1 p2 p3 l h k :=
  let p := fresh "p" in let H' := fresh H in
  inversion H as [p l h k H']; subst; clear H;
  let H'' := fresh H in inversion H' as [p1 p2 p3 H'']; subst; clear H'; rename H'' into H.

(** From H : X_Ent [|p1 $||$ p2 $||$ p3, l, h, k|], the component's predicate, as H.*)
Ltac ent_state_comp H :=
  let H' := fresh H in inversion H as [? ? ? ? H']; subst; clear H;
  let H'' := fresh H in inversion H' as [? ? ? H'']; subst; clear H'; rename H'' into H.

(***************************** Lifted tracking *****************************)

(** After a step into tfsNext, the overlap component was tfsStart or tfsNext already. It is
an overlap state before the step, as it is in a reachable entity.*)
Lemma tfsNext_prev_ent m e e' a : overlapStateEnt e -> tfsNextStateEnt m e' ->
  e -EA- a ->> e' -> tfsNextStateEnt m e \/ tfsStartStateEnt e.
Proof.
  intros OS TN S. ent_state_destr OS p1 p2 p3 l h k. ent_state_destr TN p1' p2' p3' l' h' k'.
  lets T : triple_disc_ent S. destruct T as [_ [[EQ | [b B]] _]].
  - subst p2'. left. constructor. constructor. exact TN.
  - destruct (tfsNext_prev _ _ _ _ B OS TN) as [TS | TN2]; [right | left];
      constructor; constructor; assumption.
Qed.

(***************************** Inter-Component Relationships *****************************)
(**In here, I'd like results that relate the states of things within a reachable entity e.g. the state of the software component and the mode state.*)

Lemma currEq_mode m m'' e : reachableProtEnt e ->
  currEqStateEnt m m'' e -> m = currModeEnt e. Admitted.

Lemma ovAbort_unstable e : reachableProtEnt e -> ovAbortStateEnt e -> unstable (mstEnt e).  
  (*Proof: Use some general inter-component tactics- at least pre-tactics anyway.*)
  introz U. Admitted. (*#inter-component*)
  
(** An unstable mode state changes in a step of a reachable entity only by the standard mode
switch, the mode switch to fail safe, or the overlap component aborting the mode change.*)
Lemma mState_switch_states_ent p l h k p' l' h' k' a :
  reachableProtEnt ([|p, l, h, k|]) -> unstable k -> k <> k' ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  (tfsCurrStateEnt ([|p, l, h, k|]) /\ tfsBcStateEnt ([|p', l', h', k'|])) \/
  (switchCurrStateEnt ([|p, l, h, k|]) /\ switchListenStateEnt ([|p', l', h', k'|])) \/
  (ovAbortStateEnt ([|p, l, h, k|]) /\ dormantStateEnt ([|p', l', h', k'|])) \/
  (exists m, tfsNextStateEnt m ([|p, l, h, k|]) /\ tfsNextStateEnt m ([|p', l', h', k'|])).
Proof.
  intros R U NE B.
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  (* the mode state's reads leave it as it is, and it takes a next mode only when stable *)
  inversion B; subst; try (contradiction NE; reflexivity);
    try (match goal with [K : k -ms- _ -ms> k' |- _] => inversion K; subst end;
         first [contradiction NE; reflexivity | inversion U]).
  - (* WRITE-STBL: only the overlap component writes on mStable *)
    match goal with [T : _ $||$ _ $||$ _ -PA- _ -PA> _ |- _] => triple_disc_nonTau T end.
    + exfalso. eapply bc_mStable_out_not; eassumption.
    + match goal with [T2 : p2 -PA- _ -PA> _ |- _] =>
        destruct (overlap_mStable_out _ _ T2 OS) as [[A D] | [m0 [N N']]] end.
      * right. right. left. split; constructor; constructor; assumption.
      * right. right. right. exists m0. split; constructor; constructor; assumption.
    + exfalso. eapply listen_mStable_out_not; eassumption.
  - (* CURR-WRITE: only the overlap component writes on mCurr *)
    match goal with [T : _ $||$ _ $||$ _ -PA- _ -PA> _ |- _] => triple_disc_nonTau T end.
    + exfalso. eapply bc_mCurr_out_not; eassumption.
    + match goal with [T2 : p2 -PA- _ -PA> _ |- _] =>
        destruct (ovlp_mCurr_out _ _ T2 OS) as [[A D] | [A D]] end.
      * right. left. split; constructor; constructor; assumption.
      * left. split; constructor; constructor; assumption.
    + exfalso. eapply listen_mCurr_out_not; eassumption.
Qed.

(** The current mode changes in a step of a reachable entity only when the overlap component
switches mode, from switchCurr or from tfsCurr.*)
Lemma currMode_switch_states_ent e e' a :
  reachableProtEnt e -> e -EA- a ->> e' -> currModeEnt e <> currModeEnt e' ->
  (switchCurrStateEnt e /\ switchListenStateEnt e') \/ (tfsCurrStateEnt e /\ tfsBcStateEnt e').
Proof.
  intros R B NE. destruct e as [p l h k]. destruct e' as [p' l' h' k']. simpl in NE.
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  (* only a write on mCurr changes the current mode *)
  inversion B; subst; try (contradiction NE; reflexivity);
    try (match goal with [K : k -ms- _ -ms> k' |- _] => inversion K; subst end;
         simpl in NE; contradiction NE; reflexivity).
  match goal with [T : _ $||$ _ $||$ _ -PA- _ -PA> _ |- _] => triple_disc_nonTau T end.
  - exfalso. eapply bc_mCurr_out_not; eassumption.
  - match goal with [T2 : p2 -PA- _ -PA> _ |- _] =>
      destruct (ovlp_mCurr_out _ _ T2 OS) as [[A D] | [A D]] end;
      [left | right]; split; constructor; constructor; assumption.
  - exfalso. eapply listen_mCurr_out_not; eassumption.
Qed.

(** The current mode stays across a step of a reachable entity whose overlap component is
neither switchCurr nor tfsCurr.*)
Lemma currMode_stays_ent e e' a : reachableProtEnt e -> e -EA- a ->> e' ->
  ~ switchCurrStateEnt e -> ~ tfsCurrStateEnt e -> currModeEnt e' = currModeEnt e.
Proof.
  intros R S N1 N2.
  destruct (eqDecMode (currModeEnt e') (currModeEnt e)) as [EQ | NE]; [exact EQ | exfalso].
  destruct (currMode_switch_states_ent _ _ _ R S (fun X => NE (eq_sym X)))
    as [[A _] | [A _]]; contradiction.
Qed.

(** From A : p ~p~ X and B : p ~p~ Y, for two named states X and Y of a component that differ
on a channel, a contradiction.*)
Ltac ov_disj A B :=
  let BT := fresh "BT" in
  pose proof (bisim_trans _ _ _ (bisim_symm _ _ A) B) as BT;
  prot_outProc_in_not_body; refute_by_chan BT.

(** In the tfs states that follow tfsNext, the mode state holds a fail-safe mode: as the next
mode in tfsCurr, where tfsNext has written it, and as the current mode in tfsBc and tfsListen,
once tfsCurr has switched to it.*)
Lemma tfs_failSafe_ent (e : Entity) : reachableProtEnt e ->
  (tfsCurrStateEnt e -> exists m, nextModeEnt e = Some m /\ failSafe m) /\
  (tfsBcStateEnt e -> failSafe (currModeEnt e)) /\
  (tfsListenStateEnt e -> failSafe (currModeEnt e)).
Proof.
  intro R. induction R as [e I | e e' a R IH S | e e' d R IH S].
  - (* initial: the overlap is dormant *)
    inversion I; subst.
    repeat split; intro X; exfalso; ent_state_comp X; red in X;
      prot_outProc_in_not_body; refute_by_chan X.
  - destruct IH as [IC [IB IL]].
    destruct e as [p l h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ S)
      as [p1' [p2' [p3' [l' [h' [k' [E [_ [OV _]]]]]]]]].
    subst e'.
    (* unless the overlap component switches mode, the current mode stays *)
    assert (CS : ~ switchCurrState p2 -> ~ tfsCurrState p2 ->
      currModeMState k' = currModeMState k).
    { intros N1 N2. apply (currMode_stays_ent _ _ _ R S).
      - intro Y. ent_state_comp Y. exact (N1 Y).
      - intro Y. ent_state_comp Y. exact (N2 Y). }
    repeat split; intro X; ent_state_comp X.
    + (* tfsCurr: the overlap was tfsCurr, and the mode state is as it was, or it was tfsNext
         and wrote the fail-safe successor of its mode as the next mode *)
      assert (KS : tfsCurrState p2 -> k' = k).
      { intro TC. destruct (eqDecModeState k k') as [EQ | NE]; [symmetry; exact EQ | exfalso].
        destruct (IC ltac:(constructor; constructor; exact TC)) as [m0 [NM _]].
        destruct (mState_switch_states_ent _ _ _ _ _ _ _ _ _ R (nextMode_unstable _ _ NM) NE S)
          as [[_ Y] | [[Y _] | [[Y _] | [m1 [Y _]]]]]; ent_state_comp Y;
          first [ov_disj X Y | ov_disj TC Y]. }
      assert (TC : tfsCurrState p2 \/ exists m, tfsNextState m p2).
      { destruct OV as [EQ | [b B2]]; [subst p2'; left; exact X | ].
        exact (tfsCurr_prev _ _ _ B2 OS X). }
      destruct TC as [TC | [m TN]].
      * destruct (IC ltac:(constructor; constructor; exact TC)) as [m0 [NM FS]].
        exists m0. split; [ | exact FS]. simpl in NM |- *. rewrite (KS TC). exact NM.
      * assert (ACT : forall b0, p2 -PA- b0 -PA> p2' -> exists c0 v, b0 = c0 ;! v /\
          (c0 = chanMCurrWrite \/ c0 = chanMNextWrite \/ c0 = chanMStableWrite)).
        { intros b0 B0. destruct (tfsNext_next_act _ _ _ _ B0 TN) as [[Eb _] | [Eb _]];
            subst b0; (do 2 eexists; split; [reflexivity | auto]). }
        destruct (ent_disc_proc_write _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [_ [_ CN]]]]].
        { exfalso. injection EQ; intros; subst. ov_disj TN X. }
        destruct (triple_write_ov _ _ _ _ _ _ _ PS T ACT) as [EQ | T2].
        { subst p2'. exfalso. ov_disj TN X. }
        destruct (tfsNext_next_act _ _ _ _ T2 TN) as [[Ec _] | [_ N']];
          [ | exfalso; ov_disj N' X].
        subst c. pose proof (CN (failSafeSucc m) eq_refl) as K. inversion K; subst.
        exists (failSafeSucc m). split; [reflexivity | apply failSafeSuccFS].
    + (* tfsBc: the overlap was tfsBc, and the current mode stays, or it was tfsCurr and
         switched to the next mode, which was fail-safe *)
      destruct OV as [EQ | [b B2]].
      * subst p2'. simpl. rewrite CS; [ | intro Y; ov_disj X Y | intro Y; ov_disj X Y].
        apply IB. constructor; constructor; exact X.
      * lets TC : tfsBc_prev B2 OS X.
        destruct (IC ltac:(constructor; constructor; exact TC)) as [m0 [NM FS]].
        assert (ACT : forall b0, p2 -PA- b0 -PA> p2' -> exists c0 v, b0 = c0 ;! v /\
          (c0 = chanMCurrWrite \/ c0 = chanMNextWrite \/ c0 = chanMStableWrite)).
        { intros b0 B0. destruct (tfsCurr_next_act _ _ _ B0 TC) as [[Eb _] | Y];
            [ | exfalso; ov_disj Y X].
          subst b0. do 2 eexists. split; [reflexivity | auto]. }
        destruct (ent_disc_proc_write _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [CC _]]]].
        { exfalso. injection EQ; intros; subst. ov_disj TC X. }
        destruct (triple_write_ov _ _ _ _ _ _ _ PS T ACT) as [EQ | T2].
        { subst p2'. exfalso. ov_disj TC X. }
        destruct (tfsCurr_next_act _ _ _ T2 TC) as [[Ec _] | Y]; [ | exfalso; ov_disj Y X].
        subst c. pose proof (CC eq_refl) as K. inversion K; subst.
        simpl in NM |- *. injection NM as NM. subst. exact FS.
    + (* tfsListen: the overlap was tfsListen or tfsBc, and the current mode stays *)
      assert (TL : tfsListenState p2 \/ tfsBcState p2).
      { destruct OV as [EQ | [b B2]]; [subst p2'; left; exact X | ].
        exact (tfsListen_prev _ _ _ B2 OS X). }
      simpl. destruct TL as [TL | TB].
      * rewrite CS; [ | intro Y; ov_disj TL Y | intro Y; ov_disj TL Y].
        apply IL. constructor; constructor; exact TL.
      * rewrite CS; [ | intro Y; ov_disj TB Y | intro Y; ov_disj TB Y].
        apply IB. constructor; constructor; exact TB.
  - (* a delay keeps the overlap component's tfs state, and both modes *)
    destruct IH as [IC [IB IL]].
    destruct e as [p l h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    repeat split; intro X; ent_state_destr X p1' p2' p3' l' h' k';
      lets T : triple_del_ent S; destruct T as [_ [D2 _]].
    + assert (X0 : tfsCurrState p2).
      { red. apply (overlap_del_bkwd tfsCurr _ _ _ OS D2 X).
        intros m0 e2 e3 e4 B. ovWait_bisim_contra B. }
      rewrite <- (stepTimedEnt_nextMode _ _ _ S). apply IC. constructor. constructor. exact X0.
    + assert (X0 : tfsBcState p2).
      { red. apply (overlap_del_bkwd tfsBc _ _ _ OS D2 X).
        intros m0 e2 e3 e4 B. ovWait_bisim_contra B. }
      rewrite <- (stepTimedEnt_currMode _ _ _ S). apply IB. constructor. constructor. exact X0.
    + assert (X0 : tfsListenState p2).
      { red. apply (overlap_del_bkwd tfsListen _ _ _ OS D2 X).
        intros m0 e2 e3 e4 B. ovWait_bisim_contra B. }
      rewrite <- (stepTimedEnt_currMode _ _ _ S). apply IL. constructor. constructor. exact X0.
Qed.

(**If an entity is in the tfsCurr state, then the mext mode exists and is failsafe.*)
Lemma tfsCurr_failSafe (e : Entity) :
  reachableProtEnt e -> tfsCurrStateEnt e -> exists m, nextModeEnt e = Some m /\ failSafe m.
Proof. intro R. exact (proj1 (tfs_failSafe_ent e R)). Qed.
(**GENERAL TACTICS WOULD BE USEFUL HERE, BECAUSE THERE ARE 3 FAIRLY SMILAR THEOREMS TO COME.
Proof: Look at the overlap component. Upon entering this state, it must have written out a fail safe mode
to the mode state- in particular, the successor to the current mode.*)

(**If a reachable entity is in the tfsBc state, then the current mode of that entity
is failsafe.*)
Lemma tfsBc_failSafe (e : Entity) :
  reachableProtEnt e -> tfsBcStateEnt e -> failSafe (currModeEnt e).
  (**Proof: Backtracking gives that the previous state was tfsCurrState*)
Proof. intro R. exact (proj1 (proj2 (tfs_failSafe_ent e R))). Qed.
(*then tfsCurr_failSafe gives that the next mode there was failsafe.
Finally, backtracking also gives that the transition was an output to
the mode state causing a mode switch, so the next mode of the previous state,
which was failsafe, is now the current mode.*)

(** A reachable entity whose overlap component is in tfsNext m has a current mode with the
same fail-safe successor as m. The component entered tfsNext by reading the current mode
off the mode state, and while it stays there nothing writes on mCurr. The modes themselves
need not agree: tfsNext shows its mode only through that successor (tfsNext_bisim_param).*)
Theorem tfsNext_currMode (e : Entity) (m : Mode) :
  reachableProtEnt e -> tfsNextStateEnt m e -> failSafeSucc (currModeEnt e) = failSafeSucc m.
Proof.
  intro R. revert m.
  induction R as [e I | e e' a R IH S | e e' d R IH S]; intros m TN.
  - (* initial: the overlap is dormant *)
    inversion I; subst. ent_state_comp TN. exfalso. red in TN.
    prot_outProc_in_not_body. refute_by_chan TN.
  - destruct e as [p l0 h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    ent_state_destr TN p1' p2' p3' l' h' k'.
    assert (OSE : overlapStateEnt ([|p1 $||$ p2 $||$ p3, l0, h, k|]))
      by (constructor; constructor; exact OS).
    assert (TNE0 : tfsNextStateEnt m ([|p1' $||$ p2' $||$ p3', l', h', k'|]))
      by (constructor; constructor; exact TN).
    destruct (tfsNext_prev_ent m _ _ _ OSE TNE0 S) as [TNE | TSE].
    + (* the overlap stays in tfsNext m, so the current mode is unchanged *)
      ent_state_comp TNE.
      assert (TNE' : tfsNextStateEnt m ([|p1 $||$ p2 $||$ p3, l0, h, k|]))
        by (constructor; constructor; exact TNE).
      specialize (IH m TNE'). simpl in IH |- *.
      rewrite <- IH. f_equal.
      inversion S; subst; try reflexivity;
        try (match goal with [K : _ -ms- _ -ms> _ |- _] => inversion K; subst; reflexivity end).
      (* the software wrote on mCurr: no component of the triple can *)
      exfalso.
      match goal with [TW : _ $||$ _ $||$ _ -PA- chanMCurrWrite *! -PA> _ |- _] =>
        triple_disc_nonTau TW end.
      * eapply broadcast_mCurr_out_not; eassumption.
      * match goal with [T2 : p2 -PA- _ -PA> _ |- _] =>
          destruct (bisim_disc_match _ _ _ _ TNE T2) as [q Q] end.
        unfold tfsNext in Q. invert_disc_prefixes.
      * eapply listener_mCurr_out_not; eassumption.
    + (* the overlap was tfsStart: it read the current mode *)
      ent_state_comp TSE.
      destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [_ [ACT _]]]]].
      * injection EQ; intros; subst. exfalso.
        pose proof (bisim_trans _ _ _ (bisim_symm _ _ TSE) TN) as BT.
        prot_outProc_in_not_body. refute_by_chan BT.
      * assert (ACT' : forall b, p2 -PA- b -PA> p2' -> exists v, b = chanMCurrRead ;? [baseMode v]).
        { intros b B. destruct (tfsStart_next_act _ _ _ B TSE) as [v [Eb _]]. eauto. }
        destruct (triple_mCurr_read_ov _ _ _ _ _ _ _ PS T ACT') as [EQ | [T2 [v Ec]]].
        -- subst p2'. exfalso.
           pose proof (bisim_trans _ _ _ (bisim_symm _ _ TSE) TN) as BT.
           prot_outProc_in_not_body. refute_by_chan BT.
        -- subst c. destruct (ACT v eq_refl) as [Ev Ek]. subst v k'.
           destruct (tfsStart_next_act _ _ _ T2 TSE) as [v' [Ev' TN']].
           injection Ev' as Ev'; subst v'.
           simpl. apply tfsNext_bisim_param.
           eapply bisim_trans; [apply bisim_symm; exact TN' | exact TN].
  - (* a delay: the overlap was tfsNext m already, and delay keeps the current mode *)
    destruct e as [p l0 h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    ent_state_destr TN p1' p2' p3' l' h' k'.
    lets T : triple_del_ent S. destruct T as [_ [D2 _]].
    assert (TN0 : tfsNextState m p2).
    { red. apply (overlap_del_bkwd (tfsNext m) _ _ _ OS D2 TN).
      intros m0 e2 e3 e4 B. ovWait_bisim_contra B. }
    rewrite <- (stepTimedEnt_currMode _ _ _ S). apply IH. constructor. constructor. exact TN0.
Qed.

(**If we're in the state switchCurr m', then the next mode is m'.
Corollary: switchCurr is urgent.*)
Theorem switchCurr_mState (e : Entity) :
  reachableProtEnt e -> switchCurrStateEnt e -> exists m m',
  mstEnt e = <| m, m', zeroTime |>. Admitted. (*D- reachableEnt*)
(**Proof: Inductgion on reachabledEnt.
Relies on a chain of support of similar results for switchBc, ovWait,
ovReady and init. Each one relying on the last. The ovWait and ovReady ones
would need to be proved by mutual induction.*)

Lemma tfsListen_paused p1 p2 p3 :
   tfsListenStateProt (p1 $||$ p2 $||$ p3) -> pausedStateProt (p1 $||$ p2 $||$ p3).
  Admitted. (*C*)(*Need to add process reachability as a hypothesis*)

(** If an entity inputs a message then that message is incoming.*)
Lemma input_incomingEnt (v : list BaseType) (e e' : Entity) (l : Position) (r : Distance) :
  e -EA- ([-v, l, r-]) #? ->> e' -> incomingEnt v e'.
  (*Proof: Obvious from the definition of incoming.*)
  introz U. inversion U. constructor. inversion H5.
  constructor. inversion H8. constructor.
  reflexivity. inversion H10. Qed.


(***************************** Urgency *****************************)
(**Here we prove simple urgency results which will refer to individual states rather
than more complicated predicates such as msgBadPath. The urgency results usually follow
one of two patterns. Either a synchronisation happens between two of the sub-terms in
the software process, or it happens between the software process and another component
i.e. the mode state or the interface component.*)

(*** Urgency Pre-processing Tactics ***)

Ltac urgency_pre_tac := 
  let U := fresh "U" in
  (try match goal with [ |- forall e : Entity, _] =>
  intros e e' d; introz U end); destrEnts_norm;
  match goal with [ RE : reachableProtEnt _ |- _] =>
  apply reachable_ent_prot in RE end; let q := fresh "Q" in reachprot q;
  inversion q as [p1 p2 p3 BC OV LI TR]; symmetry in TR.

(** SE SP and S are the names of the state predicates involved- the entity,
the protocol and the standard ones respectively.*)
Ltac urgency_pre_tac2 SE SP S :=
  urgency_pre_tac;
  match goal with
  | [ _ : SE ([|?p0, ?l0, ?h0, ?k0|]) |- _] =>
    assert (SP p0) as TP;
    [inversion U0; assumption | ];
    match goal with
    | [ TR : p0 = ?p1 $||$ ?p2 $||$ ?p3, TP : SP p0 |- _] =>
      rewrite TR in TP end
  end;
  match goal with [ _ : SP (?p1 $||$ ?p2 $||$ ?p3) |- _]
  (*The state predicate could come from either the broadcast, overlap, or listener.
   Try all three. Only one should succeed.*)
  => try (assert (S p1) as TS; [inversion TP; assumption | ]);
     try (assert (S p2) as TS; [inversion TP; assumption | ]);
     try (assert (S p3) as TS; [inversion TP; assumption | ]) end.

(** Same as urgency_pre_tac2 but the state predicate has 1 parameter.*)
Ltac urgency_pre_tac2_1 SE SP S :=
  urgency_pre_tac;
  match goal with
  | [ _ : SE ?x1 ([|?p0, ?l0, ?h0, ?k0|]) |- _] =>
    assert (SP x1 p0) as TP;
    [inversion U0; assumption | ];
    match goal with
    | [ TR : p0 = ?p1 $||$ ?p2 $||$ ?p3, TP : SP x1 p0 |- _] =>
      rewrite TR in TP end
  end;
  match goal with [ _ : SP ?x1 (?p1 $||$ ?p2 $||$ ?p3) |- _]
  (*The state predicate could come from either the broadcast, overlap, or listener.
   Try all three. Only one should succeed.*)
  => try (assert (S x1 p1) as TS; [inversion TP; assumption | ]);
     try (assert (S x1 p2) as TS; [inversion TP; assumption | ]);
     try (assert (S x1 p3) as TS; [inversion TP; assumption | ]) end.

(*** Urgency Results ***)

(* begin helpers for gotMsgStateEnt_urgent *)
(** A process in the gotMsg state can read any position on the channel pos.*)
Lemma gotMsgStateEnt_urgent_aux1 (p : ProcTerm) (m : Mode) (l l0 : Position) :
  gotMsgState m l p -> discActEnabled p (chanPos ;? [basePosition l0]).
  activation_tac. Qed.
(* end helpers *)

(** The listener reads its position as soon as it has a message, since the position is
always on offer: no delay in the gotMsg state.*)
Lemma gotMsgStateEnt_urgent (e e' : Entity) (d : Delay) m l :
  gotMsgStateEnt m l e -> e -ED- d ->> e' -> False.
Proof.
  intros GS DEL. destruct e as [p lp h k].
  inversion GS; subst.
  match goal with [H : gotMsgStateProt _ _ _ |- _] => inversion H; subst end.
  eapply ent_del_pos_in_not with (l0 := l); [ | eassumption].
  dae_listener. eapply gotMsgStateEnt_urgent_aux1. eassumption.
Qed.

(* begin helpers for gotRangeStateEnt_urgent *)
(** A process in the gotRange state can read any mode on the channel mCurr.*)
Lemma gotRangeStateEnt_urgent_aux1 (p : ProcTerm) (m m0 : Mode) (r : Distance) :
  gotRangeState m r p -> discActEnabled p (chanMCurrRead ;? [baseMode m0]).
  activation_tac. Qed.
(* end helpers *)

Lemma gotRangeStateEnt_urgent (e e' : Entity) (d : Delay) m r :
  gotRangeStateEnt m r e -> e -ED- d ->> e' -> False.
Proof.
  intros GS DEL. destruct e as [p l h k].
  inversion GS; subst.
  match goal with [H : gotRangeStateProt _ _ _ |- _] => inversion H; subst end.
  eapply ent_del_mCurr_in_not; [ | eassumption].
  intro m0. dae_listener.
  eapply gotRangeStateEnt_urgent_aux1. eassumption.
Qed.

(* begin helpers for currCompStateEnt_urgent *)
(** A process in the currComp state can input on mStable.*)
Lemma currCompStateEnt_urgent_aux1 (p : ProcTerm) (m : Mode) (r : Distance) :
  currCompState m r p -> discActEnabled p (chanMStableRead *?).
  activation_tac. Qed.

(** A process in the currComp state can input any mode on mNext.*)
Lemma currCompStateEnt_urgent_aux2 (p : ProcTerm) (m m0 : Mode) (r : Distance) :
  currCompState m r p -> discActEnabled p (chanMNextRead ;? [baseMode m0]).
  activation_tac. Qed.
(* end helpers *)

Lemma currCompStateEnt_urgent (e e' : Entity) (d : Delay) m r :
  currCompStateEnt m r e -> e -ED- d ->> e' -> False.
Proof.
  intros CS DEL. destruct e as [p l h k].
  inversion CS; subst.
  match goal with [H : currCompStateProt _ _ _ |- _] => inversion H; subst end.
  eapply ent_del_mStable_mNext_in_not; [ | | eassumption].
  - dae_listener. eapply currCompStateEnt_urgent_aux1. eassumption.
  - intro m0. dae_listener.
    eapply currCompStateEnt_urgent_aux2. eassumption.
Qed. (*Relies on the result that the mode state can always
EITHER output on next or stable. #modif-urgent*)

Lemma abortOvlpStateEnt_urgent (e e' : Entity) (d : Delay) :
  reachableProtEnt e -> abortOvlpStateEnt e -> e -ED- d ->> e' -> False.
  Admitted.

(** The overlap reads the current mode as soon as it is in tfsStart, since the mode state
always offers it.*)
Lemma tfsStartStateEnt_urgent : forall (e e' : Entity) (d : Delay),
  tfsStartStateEnt e -> e -ED- d ->> e' -> False.
Proof.
  intros e e' d TS DEL. ent_state_destr TS p1 p2 p3 l h k.
  eapply ent_del_sync_mState_not; [ | | exact DEL].
  - dae_overlap. eapply tfsStart_mCurr_in. exact TS.
  - apply modeState_curr_enabled.
Qed.

Lemma tfsListen_urgent : forall (e e' : Entity) (d : Delay),
  reachableProtEnt e -> tfsListenStateEnt e -> e -ED- d ->> e' 
  -> False.
  (*Some pre-tactics*)
  urgency_pre_tac2 tfsListenStateEnt tfsListenStateProt tfsListenState.
  (**It can be shown that tfsListen is only reached by the overlap when the listener
  component is paused. This in turn implies the listener component is listening on the
  channel unpause. Since the overlap component can clearly output on this channel, a
  synch is possible, and so by maximal progress delay cannot happen.*)
  lets PA : tfsListen_paused TP. assert (pausedState p3) as P3 by (inversion PA; assumption).
  lets DP : link_ent_soft_del U1. rewrite TR in DP.
  triple_del_sync_not DP (tfsListen_unpause_out _ TS) (paused_unpause_in _ P3).
Qed.

Lemma tfsNext_urgent : forall (m : Mode) (e e' : Entity) (d : Delay),
  reachableProtEnt e -> tfsNextStateEnt m e -> e -ED- d ->> e' -> False.
  intro m. intros e e' d. introz U.
  (*Need to ensure the current mode equals the parameter to tfsNext.*)
  lets TCM : tfsNext_currMode U U0.
  urgency_pre_tac2_1 tfsNextStateEnt tfsNextStateProt tfsNextState.
  assert (k0 -mtr-> failSafeSucc m) as FS2.
  simpl in TCM. rewrite <- TCM. apply failSafeSucc_successor.
  (*The mode state reads either mStable or the fail-safe successor on mNext, and the
  overlap offers both.*)
  destruct (mState_stable_next_enabled _ _ FS2) as [MS | MS];
  (eapply ent_del_sync_mState_not; [ | | eassumption]).
  - rewrite TR. dae_overlap. eapply tfsNext_mStable_out. eassumption.
  - exact MS.
  - rewrite TR. dae_overlap. eapply tfsNext_mNext_out. eassumption.
  - exact MS.
Qed.

(** The broadcaster hands its message to the interface as soon as it is in bcReady, since
the interface always takes one. So does the overlap component in ovReady.*)
Lemma bcReady_urgent (m : Mode) (l : Position) : forall (e e' : Entity) (d : Delay),
  bcReadyStateEnt m l e -> e -ED- d ->> e' -> False.
Proof.
  intros e e' d BR DEL. ent_state_destr BR p1 p2 p3 l0 h k.
  eapply ent_del_sync_inter_not; [ | | exact DEL].
  - dae_broadcast. eapply bcReady_outProc_out. exact BR.
  - apply interface_outProc_in.
Qed.

Lemma ovReady_urgent (m : Mode) (t : Exp) (l : Position) : forall (e e' : Entity) (d : Delay),
  ovReadyStateExpEnt m t l e -> e -ED- d ->> e' -> False.
Proof.
  intros e e' d OR DEL. ent_state_destr OR p1 p2 p3 l0 h k.
  eapply ent_del_sync_inter_not; [ | | exact DEL].
  - dae_overlap. eapply ovReady_outProc_out_shape. exact OR.
  - apply interface_outProc_in.
Qed.

Lemma ovAbort_urgent : forall (e e' : Entity) (d : Delay),
  reachableProtEnt e -> ovAbortStateEnt e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U.
  lets OUS : ovAbort_unstable U U0.
  urgency_pre_tac2 ovAbortStateEnt ovAbortStateProt ovAbortState.
  (**Proof: Show that the mode state is not stable whenever we
  get into this state, which will require showing that the mode state is unstable
  for init, ovWait, and ovReady- by induction on reachableProtEnt I suppose. Then
  we show that stable! is activated on ovAbort, and hence a synch can happen with
  the mode state, so by progress there is no delay possible.*)
  eapply ent_del_sync_mState_not; [ | | eassumption].
  - rewrite TR. dae_overlap. apply ovAbort_stable_out. assumption.
  - apply unstable_stable_in. exact OUS.
Qed.

(** No delay in tfsBc, whatever broadcast state the broadcaster is in, as it is in a reachable
entity: sleeping and bcWait take the overlap's output on trans, and bcReady is urgent.*)
Lemma tfsBc_urgent : forall (e e' : Entity) (d : Delay),
  broadcastStateEnt e -> tfsBcStateEnt e -> e -ED- d ->> e' -> False.
Proof.
  intros e e' d BS TB DEL. destruct e' as [p' l' h' k'].
  ent_state_destr TB p1 p2 p3 l h k. ent_state_comp BS.
  lets TOT : tfsBc_trans_out TB. lets DP : link_ent_soft_del DEL.
  destruct (broadcastState_shape _ BS) as [SL | v x BW | v1 v2 BR].
  - triple_del_sync_not DP (sleep_trans_in _ SL) TOT.
  - triple_del_sync_not DP (bcWait_trans_in_shape _ _ _ BW) TOT.
  - eapply ent_del_sync_inter_not; [ | | exact DEL].
    + dae_broadcast. eapply bcReady_outProc_out_shape. exact BR.
    + apply interface_outProc_in.
Qed.

(** No delay in switchBc, as for tfsBc: sleeping and bcWait take the overlap's output on
wake, and bcReady is urgent.*)
Lemma switchBc_urgent (m : Mode) : forall (e e' : Entity) (d : Delay),
  broadcastStateEnt e -> switchBcStateEnt m e -> e -ED- d ->> e' -> False.
Proof.
  intros e e' d BS SB DEL. destruct e' as [p' l' h' k'].
  ent_state_destr SB p1 p2 p3 l h k. ent_state_comp BS.
  lets TOT : switchBc_wake_out SB. lets DP : link_ent_soft_del DEL.
  destruct (broadcastState_shape _ BS) as [SL | v x BW | v1 v2 BR].
  - triple_del_sync_not DP (sleeping_wake_in m _ SL) TOT.
  - triple_del_sync_not DP (bcWait_wake_in_shape m _ _ _ BW) TOT.
  - eapply ent_del_sync_inter_not; [ | | exact DEL].
    + dae_broadcast. eapply bcReady_outProc_out_shape. exact BR.
    + apply interface_outProc_in.
Qed.

Lemma swithcCurr_urgent (m : Mode) : forall (e e' : Entity) (d : Delay),
  reachableProtEnt e -> switchCurrStateEnt e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U. lets Q : U.
  urgency_pre_tac2 switchCurrStateEnt switchCurrStateProt switchCurrState.
  (*Apply (switchCurr-next-Mode) to assert that there is some next mode.*)  
  lets SMS : switchCurr_mState U U0. decompEx2 SMS m1 m2 MS.
  (*Then it is easy to show that the mode state is capable of inputting
  on mCurr, which complements the output that is enabled in this state,
  and so we're urgent.*)
  eapply ent_del_sync_mState_not; [ | | eassumption].
  - rewrite TR. dae_overlap. apply switchCurr_mCurr_out. assumption.
  - simpl in MS. rewrite MS. apply mst_tout_mCurr_in.
Qed.

Lemma switchListen_urgent : forall (e e' : Entity) (d : Delay),
  reachableProtEnt e -> switchListenStateEnt e -> e -ED- d ->> e' 
  -> False. urgency_pre_tac2 switchListenStateEnt switchListenStateProt
  switchListenState.
  (*We use (paused_switch) to show that the listener component is paused*)
  assert (switchStateProt p0) as SP. rewrite TR. constructor. apply switLisSt.
  assumption. lets PS : paused_switch U. rewrite <- PS in SP. rewrite TR in SP.
  assert (pausedState p3) as PS3. inversion SP. assumption.
  (*Now a synchronisation is shown on unpause.*)
  lets DP : link_ent_soft_del U1. rewrite TR in DP.
  triple_del_sync_not DP (switchListen_unpause_out _ TS) (paused_unpause_in _ PS3).
Qed.


(***************************** Positions *****************************)
(** A component about to broadcast a position is at that position: it read the position
from the entity, no discrete step moves an entity, and no delay is possible in the
meantime, since the state is urgent.*)

(** If an entity is in a state ready to output some m l from the broadcast component,
then it is in the position l.*)
Theorem bcReady_pos (e : Entity) (m : Mode) (l : Position) :
  reachableProtEnt e -> bcReadyStateEnt m l e -> posEnt e = l.
Proof.
  intro R. revert m l.
  induction R as [e I | e e' a R IH S | e e' d R IH S]; intros m l BR.
  - (* initial: the broadcaster is sleeping *)
    inversion I; subst. ent_state_comp BR. exfalso. red in BR.
    prot_outProc_in_not_body. refute_by_chan BR.
  - (* a discrete step: the broadcaster was in bcReady already, or read the position *)
    destruct e as [p l0 h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    ent_state_destr BR p1' p2' p3' l' h' k'.
    lets PP : stepEnt_disc_pres_pos S. simpl in PP. subst l'.
    assert (IH' : bcReadyState m l p1 -> l0 = l).
    { intro B. exact (IH m l ltac:(constructor; constructor; exact B)). }
    destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [ACT _]]]].
    + inversion EQ; subst. simpl. apply IH'. exact BR.
    + assert (ACT' : forall b, p1 -PA- b -PA> p1' -> b = chanPos ;? [basePosition l]) by
        (intros b B; eapply bcReady_prev; eassumption).
      destruct (triple_pos_read_bc _ _ _ _ _ _ _ _ PS T ACT') as [EQ | EQ].
      * subst p1'. simpl. apply IH'. exact BR.
      * simpl. symmetry. apply (ACT l). exact EQ.
  - (* a delay: sleeping and bcWait never delay into bcReady, and bcReady is urgent *)
    destruct e as [p l0 h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    ent_state_destr BR p1' p2' p3' l' h' k'.
    lets T : triple_del_ent S. destruct T as [D1 _]. exfalso.
    destruct (broadcastState_shape _ BS) as [B | m0 e0 B | m0 l1 B].
    + assert (BX : p1' ~p~ sleeping) by
        (eapply bisim_del_pres; [del_self_body | exact B | exact D1]).
      pose proof (bisim_trans _ _ _ (bisim_symm _ _ BX) BR) as BT.
      prot_outProc_in_not_body. refute_by_chan BT.
    + destruct (bisim_step_del _ _ _ _ B D1) as [q [TQ BQ]].
      destruct (bcWait_del_shape _ _ _ _ TQ) as [e1 B'].
      pose proof (bisim_trans _ _ _ (bisim_symm _ _ B')
        (bisim_trans _ _ _ (bisim_symm _ _ BQ) BR)) as BT.
      prot_outProc_in_not_body. refute_by_chan BT.
    + eapply bcReady_urgent with (e := [|p1 $||$ p2 $||$ p3, l0, h, k|]); [ | exact S].
      constructor. constructor. exact B.
Qed.

(** If an entity is in a state ready to output some m l from the overlap component,
then it is in the position l. The timer is any expression, well formed or not: it plays no
part, and a reachable overlap component may hold an ill-formed one (see ovReadyStateExp).*)
Theorem ovReady_pos (e : Entity) (m : Mode) (t : Exp) (l : Position) :
  reachableProtEnt e -> ovReadyStateExpEnt m t l e -> posEnt e = l.
Proof.
  intro R. revert m t l.
  induction R as [e I | e e' a R IH S | e e' d R IH S]; intros m t l OR.
  - (* initial: the overlap component is dormant *)
    inversion I; subst. ent_state_comp OR. exfalso. red in OR.
    prot_outProc_in_not_body. refute_by_chan OR.
  - (* a discrete step: the overlap component was in ovReady already, or read the position *)
    destruct e as [p l0 h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    ent_state_destr OR p1' p2' p3' l' h' k'.
    lets PP : stepEnt_disc_pres_pos S. simpl in PP. subst l'.
    assert (IH' : ovReadyStateExp m t l p2 -> l0 = l).
    { intro B. exact (IH m t l ltac:(constructor; constructor; exact B)). }
    destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [ACT _]]]].
    + inversion EQ; subst. simpl. apply IH'. exact OR.
    + assert (ACT' : forall b, p2 -PA- b -PA> p2' -> b = chanPos ;? [basePosition l]) by
        (intros b B; eapply ovReady_prev_act; eassumption).
      destruct (triple_pos_read_ov _ _ _ _ _ _ _ _ PS T ACT') as [EQ | EQ].
      * subst p2'. simpl. apply IH'. exact OR.
      * simpl. symmetry. apply (ACT l). exact EQ.
  - (* a delay: only ovWait delays into another state, and ovReady is urgent *)
    destruct e as [p l0 h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    ent_state_destr OR p1' p2' p3' l' h' k'.
    lets T : triple_del_ent S. destruct T as [_ [D2 _]]. exfalso.
    assert (OB : p2 ~p~ ovReady m t l).
    { eapply overlap_del_bkwd; [exact OS | exact D2 | exact OR | ].
      intros m0 e2 e3 e4 B. ovWait_bisim_contra B. }
    eapply ovReady_urgent with (e := [|p1 $||$ p2 $||$ p3, l0, h, k|]); [ | exact S].
    constructor. constructor. exact OB.
Qed.

(***************************** Path predicates *****************************)(***************************** Path predicates *****************************)
(**In here, results about the path predicates. Mostly what we're concerned
with is preservation of the path predicates.*)

(*IF THIS SECTION GETS LARGE, WE CAN MIGRATE TO A SEPARATE PATH PREDICATE FILE*)

(*Develop general tactics for the path predicates?*)

Lemma msgAbortPathEnt_urgent e e' d :
  reachableProtEnt e -> msgAbortPathEnt e ->
  e -ED- d ->> e' -> False. intro.
  introz U. inversion U; subst.
  (*Inversion and then lift individual-stae urgency results.*)
  assert (gotMsgStateEnt m'' l' ([|p, l, h, k|])).
  econstructor; eassumption.
  eapply gotMsgStateEnt_urgent; eassumption.
  assert (gotRangeStateEnt m'' r ([|p, l, h, k|])).
  econstructor; eassumption.
  eapply gotRangeStateEnt_urgent; eassumption.
  assert (currCompStateEnt m'' r ([|p, l, h, k|])).
  econstructor; eassumption.  
  eapply currCompStateEnt_urgent; eassumption.
  assert (abortOvlpStateEnt ([|p, l, h, k|])).
  econstructor; eassumption.  
  eapply abortOvlpStateEnt_urgent; eassumption. Qed.

(** The interface component is irrelevant to the msgAbortPath.*)
Lemma msgAbort_inter_irrel p l h h' k :
  msgAbortPathEnt ([|p, l, h, k|]) ->
  msgAbortPathEnt ([|p, l, h', k|]).
Proof.
  intro H. inversion H; subst.
  - eapply mapMsg; try reflexivity; eassumption.
  - eapply mapGrng; try reflexivity; eassumption.
  - eapply mapCuco; eassumption.
  - eapply mapAbort; eassumption.
Qed.  

(***************************** Delay Behaviour *****************************)

(**A reachable entity that can delay is in the listening state.*)
Theorem del_listening_pre (e e' : Entity) (d : Delay) :
  reachableProtEnt e -> e -ED- d ->> e' -> 
  abortOvlpStateEnt e \/ badOvlpStateEnt e \/ listeningStateEnt e \/ pausedStateEnt e.
  introz U. Admitted. (*D- reachableEnt*)
(**Proof: Since the entity is reachable, we know it has a listener
component (...reachableProt_triple...), so we do a case analysis as to what the location
of the listener component is. In most cases, we can show by simple urgency results that
a discrete action is possible via the listener synchronising with another component of
the entity. The remaining cases that aren't urgent are exactly the conclusion to this
result, and we're done.*)

(*Gives the possible states of the overlap component if a delay is possible.*)
Theorem del_ovlp (e e' : Entity) (d : Delay) : 
  reachableProtEnt e -> e -ED- d ->> e' ->
  dormantStateEnt e \/ tfsCurrStateEnt e \/
  exists m, exists t, exists x, exists y, ovWaitStateEnt m t x y e . Admitted. (*D- reachableEnt*)
(**Proof: Case analyse the overlap component of the software
process in e and eliminate most other possibilities by simple urgency results.
For the tfsListen case, apply (del_listening_pre). A corollary of this is that
the listener component is always capable of input on unpause or output on bad
or abort, and since tfsListen can do all three, a synch is always possible,
hence our urgency by progress. This should cover all states except those in our
conclusion, and we're done.*)

(**A reachable entity that can delay is in the listening state.*)
Theorem del_listening (e e' : Entity) (d : Delay) :
  reachableProtEnt e -> e -ED- d ->> e' -> listeningStateEnt e. Admitted. (*D- reachableEnt*)
(**Proof: First we apply (del_listening_pre), to get that
we are either in abortOvlp, badOvlp, paused or listening. If the last case
is true, then we are done. From here, we apply (del_ovlp) to further get
dormant, tfsCurr or ovWait as possibilities for the current state. Now,
if we are paused, then by (paused_switch) we are switchState- but this
contradicts the three possibilities for an overlap state, so it must be
thrown away. Hence we are either abortOvlp or badOvlp. But all three overlap
possibilities can input on both abort and bad, so in all six cases a synchronisation
is possible. Hence we arrive at our contradiction and conclude listening.
>Could use more automation in the tactic maybe? Pull out the software component,
apply the two previous results, and run some sort of auto that eliminates all the
cases that can synch.*)

(***************************** Lifted State Predicate Results *****************************)

Lemma switchCurr_switch_ent (e : Entity) :
  switchCurrStateEnt e -> switchStateEnt e. intros. 
  inversion H. inversion H0. do 2 constructor.
  apply switCurSt. assumption. Qed.

(*LOCAL TIDY*)

(** A step of an entity whose listener is in currOK: the listener stays, read stable and is
listening, or read the next mode m' off the mode state and is in nextEq m' m''.*)
Theorem currOK_track_ent (e e' : Entity) (a : ActDiscEnt) (m'' : Mode) :
  reachableProtEnt e -> currOKStateEnt m'' e -> e -EA- a ->> e' ->
  currOKStateEnt m'' e' \/ listeningStateEnt e' \/
  exists m', nextEqStateEnt m' m'' e' /\ nextModeEnt e = Some m'.
Proof.
  intros R G S. destruct e as [p l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  ent_state_comp G.
  destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ S) as [p1' [p2' [p3' [l' [h' [k' [E _]]]]]]].
  subst e'.
  destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [_ [_ ACT]]]]].
  - injection EQ; intros; subst. left. constructor. constructor. exact G.
  - destruct c as [c0 v0 | c0 v0 | ].
    + (* an input of the triple is an input of one component *)
      triple_disc_nonTau T; try (left; constructor; constructor; exact G).
      match goal with [T3 : _ -PA- c0 ;? v0 -PA> _ |- _] =>
        destruct (currOK_next_act _ _ _ _ T3 G) as [[Ea L] | [v [Ea N]]] end.
      * right. left. constructor. constructor. exact L.
      * injection Ea; intros; subst. destruct (ACT v eq_refl) as [NM _].
        right. right. exists v. split; [constructor; constructor; exact N | exact NM].
    + (* currOK does not output *)
      triple_disc_nonTau T; try (left; constructor; constructor; exact G).
      match goal with [T3 : _ -PA- c0 ;! v0 -PA> _ |- _] =>
        destruct (currOK_next_act _ _ _ _ T3 G) as [[Ea L] | [v [Ea N]]] end; discriminate.
    + (* a tau: no other component writes on the channels the listener reads *)
      destruct (link_reach_triple_tau _ _ _ _ _ _ T PS) as [c0 [v0 H]].
      decompose [or and] H; clear H;
      try match goal with [E : p3 = p3' |- _] =>
        subst p3'; left; constructor; constructor; exact G end;
      try match goal with [H1 : p3 -PA- _ ;! _ -PA> p3' |- _] =>
        destruct (currOK_next_act _ _ _ _ H1 G) as [[X _] | [? [X _]]]; discriminate X end;
      match goal with [H1 : p3 -PA- ?c1 ;? ?v1 -PA> p3' |- _] =>
        destruct (currOK_next_act _ _ _ _ H1 G) as [[X L] | [v [X N]]];
        injection X as X1 X2; subst c1 v1 end; exfalso;
      first
        [ match goal with [H2 : p1 -PA- _ ;! _ -PA> _ |- _] =>
            eapply broadcast_read_out_not; [exact BS | | exact H2]; solve [auto] end
        | match goal with [H2 : p2 -PA- _ ;! _ -PA> _ |- _] =>
            eapply overlap_read_out_not; [exact OS | | exact H2]; solve [auto] end ].
Qed.

Lemma nextMode_ent_mState p l h k m :
  nextModeEnt ([|p, l, h, k|]) = Some m -> nextModeMState k = Some m.
Proof.
  intro U. exact U.
Qed.

Ltac ent_disc_pres_pos_tac := match goal with
  [V : [|_, ?l, _, _|] -EA- ?b ->> [|_, ?l', _, _|] |- _ ] =>
  let EDP := fresh "EDP" in
  lets EDP : stepEnt_disc_pres_pos V; simpl in EDP end.

Lemma gotMsg_gotRange_track_ent (m m' : Mode) (l l' l1 : Position)
  (r : Distance) (p p' : ProcTerm) h h' k k' a :
  gotMsgStateEnt m l1 ([|p, l, h, k|]) ->
  gotRangeStateEnt m' r ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  l = l' /\ m = m' /\
  r = {| distance := dist2d l l1 -nn- speedMax *nn* msgLatency |}.
  Admitted.
(*Proof: Entity tracking result: possibly use generic tactic? Use software tracking
result? Use inter-component relationship result/tactics?*)
(*+*)
(** A step of an entity whose listener is in gotRange: the listener stays, or it read the
current mode off the mode state and is in currPincCheck with it. Bisimilar currPincCheck
need not agree on their parameters, so the lemma states the derivative's state rather than
equalities between parameters.*)
Theorem gotRange_track_ent (e e' : Entity) (a : ActDiscEnt) (m2 : Mode) (r : Distance) :
  reachableProtEnt e -> gotRangeStateEnt m2 r e -> e -EA- a ->> e' ->
  gotRangeStateEnt m2 r e' \/ currPincCheckStateEnt (currModeEnt e) m2 r e'.
Proof.
  intros R G S. destruct e as [p l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  ent_state_comp G.
  destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ S) as [p1' [p2' [p3' [l' [h' [k' [E _]]]]]]].
  subst e'.
  destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [_ [ACT _]]]]].
  - injection EQ; intros; subst. left. constructor. constructor. exact G.
  - assert (ACT' : forall b, p3 -PA- b -PA> p3' -> exists v, b = chanMCurrRead ;? [baseMode v]).
    { intros b B. destruct (gotRange_next_act _ _ _ _ _ B G) as [v [Eb _]]. eauto. }
    destruct (triple_mCurr_read_li _ _ _ _ _ _ _ PS T ACT') as [EQ | [T3 [v Ec]]].
    + subst p3'. left. constructor. constructor. exact G.
    + subst c. destruct (ACT v eq_refl) as [Ev _]. subst v.
      destruct (gotRange_next_act _ _ _ _ _ T3 G) as [v' [Ev' C]].
      injection Ev' as Ev'; subst v'.
      right. simpl. constructor. constructor. exact C.
Qed.

(** A step of an entity whose listener is in rangeBad: the listener stays, or it read the
current mode off the mode state and is in currEq with it.*)
Theorem rangeBad_track_ent (e e' : Entity) (a : ActDiscEnt) (m2 : Mode) :
  reachableProtEnt e -> rangeBadStateEnt m2 e -> e -EA- a ->> e' ->
  rangeBadStateEnt m2 e' \/ currEqStateEnt (currModeEnt e) m2 e'.
Proof.
  intros R G S. destruct e as [p l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  ent_state_comp G.
  destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ S) as [p1' [p2' [p3' [l' [h' [k' [E _]]]]]]].
  subst e'.
  destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S) as [EQ | [c [T [_ [ACT _]]]]].
  - injection EQ; intros; subst. left. constructor. constructor. exact G.
  - assert (ACT' : forall b, p3 -PA- b -PA> p3' -> exists v, b = chanMCurrRead ;? [baseMode v]).
    { intros b B. destruct (rangeBad_next_act _ _ _ _ B G) as [v [Eb _]]. eauto. }
    destruct (triple_mCurr_read_li _ _ _ _ _ _ _ PS T ACT') as [EQ | [T3 [v Ec]]].
    + subst p3'. left. constructor. constructor. exact G.
    + subst c. destruct (ACT v eq_refl) as [Ev _]. subst v.
      destruct (rangeBad_next_act _ _ _ _ T3 G) as [v' [Ev' C]].
      injection Ev' as Ev'; subst v'.
      right. simpl. constructor. constructor. exact C.
Qed.
(*+*)
Lemma currComp_listening_track_ent m'' r l l' p p' h h' k k' a :
  currCompStateEnt m'' r ([|p, l, h, k|]) ->
  listeningStateEnt ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  k -ms- chanMStableRead @! -ms> k' /\ h = h'. Admitted.
  (*Add entity-level tracking result.*)
(*+*)
Lemma currComp_nextPincCheck_track_ent (m2 m1' m2' : Mode) (l l' : Position)
  (r r' : Distance) (p p' : ProcTerm) h h' k k' a :
  currCompStateEnt m2 r ([|p, l, h, k|]) ->
  nextPincCheckStateEnt m1' m2' r' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  m2 = m2' /\ r = r' /\ nextModeMState k = Some m1'.
  Admitted.

Lemma ovReady_ovWait_track_ent m m' t t' x' y' l0 a
  p p' l l' h h' k k' :
  ovReadyStateEnt m t l0 ([|p, l, h, k|]) ->
  ovWaitStateEnt m' t' x' y' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p -PA- chanOutProc ;! [baseMode m, basePosition l0] -PA> p' /\
  h -i- chanOutProc {? [baseMode m, basePosition l0] -i> h' /\
  k = k' /\ m = m' /\ l = l0.
  (*Some aspects of the proof e.g. l = l0 may require separate results.
  Maybe they already exist?*)Admitted.

(* begin helpers for tfsNext_next_ent *)
Lemma tfsNext_next_ent_currN : ProcEquiv.bisimulation (tfsCurrN $([])$) tfsCurr.
Proof. apply app_bisim_nil. reflexivity. Qed.

Lemma tfsNext_next_ent_nextN (m : Mode) :
  ProcEquiv.bisimulation (tfsNextN $([eBase (baseMode m)])$) (tfsNext m).
Proof.
  replace (tfsNext m)
    with (subProcTerm (listsToSub [vM] [eBase (baseMode m)]) (tfsNext (eVar vM))).
  - apply app_bisim_def. reflexivity.
  - unfold tfsNext. simpl. unfold update. unfold varEq.
    destruct (varEqDec vM vM) as [_ | C]; [reflexivity | contradiction C; reflexivity].
Qed.

Lemma tfsNext_next_ent_proc m p p' b : tfsNextState m p -> p -PA- b -PA> p' ->
  tfsNextState m p' \/ tfsCurrState p'.
Proof.
  unfold tfsNextState, tfsCurrState. intros B T.
  destruct (bisim_step_disc _ _ _ _ B T) as [q [Tq Bq]].
  unfold tfsNext in Tq. inversion Tq; subst.
  - match goal with [V : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion V; subst end.
    right. eapply ProcEquiv.bisim_trans; [eassumption | apply tfsNext_next_ent_currN].
  - match goal with [V : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion V; subst end.
    left. eapply ProcEquiv.bisim_trans; [eassumption | apply tfsNext_next_ent_nextN].
Qed.
(* end helpers *)

Lemma tfsNext_next_ent e e' a m :
  e -EA- a ->> e' -> tfsNextStateEnt m e ->
  tfsNextStateEnt m e' \/ tfsCurrStateEnt e'.
Proof.
  intros T N. destruct e as [p l h k]. destruct e' as [p' l' h' k'].
  inversion N as [p0 l0 h0 k0 NP]; subst.
  inversion NP as [p1 p2 p3 NP2]; subst.
  destruct (link_ent_soft_disc _ _ _ _ _ _ _ _ _ T) as [E | [b TP]].
  - subst. left. constructor. constructor. assumption.
  - link_partripdiscex_tac E p1' p2' p3'. subst.
    link_partripdiscW2_tac TP W. destruct W as [E2 | [b' T2]]; subst.
    + left. constructor. constructor. assumption.
    + destruct (tfsNext_next_ent_proc _ _ _ _ NP2 T2) as [X | X].
      * left. constructor. constructor. assumption.
      * right. constructor. constructor. assumption.
Qed.

(* begin helpers for tfsCurr_next_ent *)
(** Support for the #fwd-track-lift-ent family (tfsCurr/tfsBc/tfsListen _next_ent):
forward tracking of an overlap-component state predicate, lifted from single
process terms (where the state predicates are bisimilarity classes) to entities.*)

(** Generic lifting: a forward-tracking result for an overlap state predicate X
lifts from process terms to entities.*)
Lemma tfsCurr_next_ent_lift (X Y : ProcTerm -> Prop) e e' a :
  (forall q q' b, q -PA- b -PA> q' -> X q -> X q' \/ Y q') ->
  e -EA- a ->> e' -> liftProcEnt (liftOverlap X) e ->
  liftProcEnt (liftOverlap X) e' \/ liftProcEnt (liftOverlap Y) e'.
Proof.
  intros F S L. inversion L as [p l h k LO]; subst.
  inversion LO as [p1 p2 p3 X2]; subst.
  lets T : triple_disc_ent_fwd S.
  destruct T as [p1' [p2' [p3' [l' [h' [k' [EQ [_ [[E | [b B]] _]]]]]]]]]; subst e'.
  - subst p2'. left. constructor. constructor. assumption.
  - destruct (F _ _ _ B X2) as [Z | Z]; [left | right];
      constructor; constructor; exact Z.
Qed.

(** Closes a goal [S p'] (S a bisimilarity-class state predicate) from a
hypothesis [p' ~p~ n $(l)$] by unfolding the application.*)
Ltac tfsCurr_next_ent_close_tac :=
  match goal with [B1 : ProcEquiv.bisimulation ?p' ?q' |- _] =>
    hnf; eapply ProcEquiv.bisim_trans; [exact B1 | ];
    eapply ProcEquiv.bisim_trans; [apply app_bisim | ];
    rewrite unfoldApp_body; clean_proc; apply ProcEquiv.bisim_refl
  end.

(** Process-level forward tracking for a goal of the form
[p -PA- b -PA> p' -> S p -> S1 p' \/ ... \/ Sn p'], where S, S1..Sn are
bisimilarity-class state predicates and the body of S is a sum of prefixes
whose continuations are name applications.*)
Ltac tfsCurr_next_ent_fwd_tac :=
  let S := fresh "S" in let B := fresh "B" in
  intros S B; hnf in B;
  let q' := fresh "q'" in let S1 := fresh "S1" in let B1 := fresh "B1" in
  destruct (bisim_step_disc _ _ _ _ B S) as [q' [S1 B1]];
  clear S B;
  try unfold tfsCurr in S1; try unfold tfsBc in S1; try unfold tfsListen in S1;
  repeat invert_trans; simpl in B1;
  repeat match goal with [ |- _ \/ _ ] =>
    first [left; solve [tfsCurr_next_ent_close_tac] | right] end;
  tfsCurr_next_ent_close_tac.

(** Process-level forward tracking from the tfsCurr state.*)
Lemma tfsCurr_next_ent_aux p p' b :
  p -PA- b -PA> p' -> tfsCurrState p -> tfsCurrState p' \/ tfsBcState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsCurr_next_ent e e' a :
  e -EA- a ->> e' -> tfsCurrStateEnt e ->
  tfsCurrStateEnt e' \/ tfsBcStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsCurrState tfsBcState _ _ _ tfsCurr_next_ent_aux S T).
Qed.

(** From tfsStart, the overlap component reads the current mode and moves to tfsNext with
it. The mode it reads is a mode because inputs are typed: it comes from the mode state, or
from another component writing a mode on mCurr.*)
Lemma tfsStart_next_ent e e' a :
  e -EA- a ->> e' -> tfsStartStateEnt e ->
  tfsStartStateEnt e' \/ exists m, tfsNextStateEnt m e'.
Proof.
  intros T S.
  destruct (tfsCurr_next_ent_lift tfsStartState (fun q => exists m, tfsNextState m q)
    e e' a (fun q q' b T' S' => or_intror (tfsStart_next q q' b T' S')) T S) as [X | X].
  - left. exact X.
  - right. inversion X as [p l h k LO]; subst. inversion LO as [p1 p2 p3 [m M]]; subst.
    exists m. constructor. constructor. exact M.
Qed.

(* begin helpers for tfsBc_next_ent *)
(** Process-level forward tracking from the tfsBc state
(uses the #fwd-track-lift-ent support from tfsCurr_next_ent).*)
Lemma tfsBc_next_ent_aux p p' b :
  p -PA- b -PA> p' -> tfsBcState p -> tfsBcState p' \/ tfsListenState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsBc_next_ent e e' a :
  e -EA- a ->> e' -> tfsBcStateEnt e ->
  tfsBcStateEnt e' \/ tfsListenStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsBcState tfsListenState _ _ _ tfsBc_next_ent_aux S T).
Qed.

(* begin helpers for tfsListen_next_ent *)
(** Process-level forward tracking from the tfsListen state
(uses the #fwd-track-lift-ent support from tfsCurr_next_ent).*)
Lemma tfsListen_next_ent_aux p p' b :
  p -PA- b -PA> p' -> tfsListenState p -> tfsListenState p' \/ dormantState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsListen_next_ent e e' a :
  e -EA- a ->> e' -> tfsListenStateEnt e ->
  tfsListenStateEnt e' \/ dormantStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsListenState dormantState _ _ _ tfsListen_next_ent_aux S T).
Qed.

(*- LOCAL TIDY*)