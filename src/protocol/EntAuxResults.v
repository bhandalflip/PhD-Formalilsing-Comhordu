(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Lra.
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

(** In a reachable entity, a component of the triple that can only have changed by acting on
one of the entity's channels either stayed as it was, or met the rest of the entity: put alone
in the entity, it makes the same step. This is ent_disc_comp_chan, since the protocol uses its
channels correctly.*)
Lemma triple_disc_ent_chan {p1 p2 p3 p1' p2' p3' l l' h h' k k' a} i {x x'} :
  reachableProtEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]) ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- a ->> [|p1' $||$ p2' $||$ p3', l', h', k'|] ->
  nth_error [p1, p2, p3] i = Some x -> nth_error [p1', p2', p3'] i = Some x' ->
  (forall b, x -PA- b -PA> x' -> entChanAct b) ->
  x = x' \/ [|x, l, h, k|] -EA- a ->> [|x', l', h', k'|].
Proof.
  intros R S Nx Nx' ACT.
  lets CU : reachableProt_correctChannelUsage (reachable_ent_prot _ _ _ _ R).
  destruct (ent_disc_comp_chan _ _ p1 [p2, p3] p1' [p2', p3'] _ _ _ _ _ _ _ _ _ _
    CU S eq_refl Nx Nx' ACT) as [E | St]; [left; exact E | right].
  destruct (stepAt_nth_error_eq _ _ _ _ St) as [y [y' [Ny [Ny' Y]]]].
  assert (y = x) by congruence. assert (y' = x') by congruence. subst. exact Y.
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

(** The mode state stays across a step of a reachable entity while it is unstable, unless the
overlap component writes on it, from tfsCurr, switchCurr, ovAbort or tfsNext.*)
Lemma mState_stays_ent p1 p2 p3 l h k p1' p2' p3' l' h' k' a :
  reachableProtEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]) -> unstable k ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- a ->> [|p1' $||$ p2' $||$ p3', l', h', k'|] ->
  ~ tfsCurrState p2 -> ~ switchCurrState p2 -> ~ ovAbortState p2 ->
  (forall m, ~ tfsNextState m p2) -> k' = k.
Proof.
  intros R U S N1 N2 N3 N4.
  destruct (eqDecModeState k k') as [EQ | NE]; [symmetry; exact EQ | exfalso].
  destruct (mState_switch_states_ent _ _ _ _ _ _ _ _ _ R U NE S)
    as [[Y _] | [[Y _] | [[Y _] | [m1 [Y _]]]]]; ent_state_comp Y.
  - exact (N1 Y).
  - exact (N2 Y).
  - exact (N3 Y).
  - exact (N4 m1 Y).
Qed.

(** Before a step into init, ovWait, ovReady or ovAbort, the overlap component was in one of
these states already, or was dormant and read the next mode.*)
Local Lemma pendingOvlp_prev p p' b : overlapState p -> p -PA- b -PA> p' ->
  (exists m, initState m p') \/ (exists m t x y, ovWaitStateExp m t x y p') \/
  (exists m t l, ovReadyStateExp m t l p') \/ ovAbortState p' ->
  ((exists m, initState m p) \/ (exists m t x y, ovWaitStateExp m t x y p) \/
   (exists m t l, ovReadyStateExp m t l p) \/ ovAbortState p) \/
  (dormantState p /\ exists v, b = chanMNextRead ;? [baseMode v]).
Proof.
  intros O TR [[m SP] | [[m [t [x [y SP]]]] | [[m [t [l SP]]] | SP]]]; red in SP;
    backtrack_shape SP;
    first [ right; split; [exact B | eexists; reflexivity]
          | exfalso; exact (tfsStart_not_init m BT)
          | left; left; eexists; exact B
          | left; right; left; do 4 eexists; exact B
          | left; right; right; left; do 3 eexists; exact B ].
Qed.

(** Only a state of init, ovWait, ovReady or ovAbort delays into one.*)
Local Lemma pendingOvlp_del_bkwd p p' d : overlapState p -> p -PD- d -PD> p' ->
  (exists m, initState m p') \/ (exists m t x y, ovWaitStateExp m t x y p') \/
  (exists m t l, ovReadyStateExp m t l p') \/ ovAbortState p' ->
  (exists m, initState m p) \/ (exists m t x y, ovWaitStateExp m t x y p) \/
  (exists m t l, ovReadyStateExp m t l p) \/ ovAbortState p.
Proof.
  intros OS D [[m SP] | [[m [t [x [y SP]]]] | [[m [t [l SP]]] | SP]]].
  - left. exists m. red. apply (overlap_del_bkwd (init m) _ _ _ OS D SP).
    intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
  - right. left. destruct (ovWait_del_bkwd _ _ _ _ _ _ _ OS D SP) as [m0 [f2 [f3 [f4 [B _]]]]].
    exists m0 f2 f3 f4. exact B.
  - right. right. left. exists m t l. red. apply (overlap_del_bkwd (ovReady m t l) _ _ _ OS D SP).
    intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
  - right. right. right. red. apply (overlap_del_bkwd ovAbort _ _ _ OS D SP).
    intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
Qed.

(** Refutes X : p ~p~ A and Y : p ~p~ B for named states A and B that differ on a channel.*)
Local Ltac ov_states_disj X Y :=
  let BT := fresh "BT" in pose proof (bisim_trans _ _ _ (bisim_symm _ _ X) Y) as BT;
  prot_outProc_in_not_body; unfold liftNameProc, liftVarList in BT; refute_by_chan BT.

(** Refutes X, that the overlap component is in init, ovWait, ovReady or ovAbort, against
Y : p ~p~ B for a named state B outside them.*)
Local Ltac pending_disj X Y :=
  destruct X as [[? X] | [[? [? [? [? X]]]] | [[? [? [? X]]] | X]]]; ov_states_disj X Y.

(** In a reachable entity whose overlap component is in init, ovWait, ovReady or ovAbort, a mode
change is pending: the mode state is unstable.*)
Lemma pendingOvlp_unstable_ent (e : Entity) : reachableProtEnt e ->
  liftProcEnt (liftOverlap (fun p => (exists m, initState m p) \/
    (exists m t x y, ovWaitStateExp m t x y p) \/ (exists m t l, ovReadyStateExp m t l p) \/
    ovAbortState p)) e -> unstable (mstEnt e).
Proof.
  intro R. induction R as [e I | e e' a R IH S | e e' d R IH S]; intro X.
  - (* initial: the overlap is dormant *)
    inversion I; subst. ent_state_comp X. exfalso. cbv beta in X.
    pose proof (bisim_refl dormant) as D. pending_disj X D.
  - destruct e as [p l h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ S)
      as [p1' [p2' [p3' [l' [h' [k' [E [_ [OV _]]]]]]]]].
    subst e'. ent_state_comp X. cbv beta in X. simpl.
    destruct (Classical_Prop.classic ((exists m, initState m p2) \/
      (exists m t x y, ovWaitStateExp m t x y p2) \/ (exists m t l, ovReadyStateExp m t l p2) \/
      ovAbortState p2)) as [BP | NBP].
    + (* the overlap was in one of these states: the mode state was unstable, and stays so *)
      assert (U : unstable k) by (apply IH; constructor; constructor; exact BP).
      destruct (eqDecModeState k k') as [EQk | NEk]; [subst k'; exact U | exfalso].
      destruct (mState_switch_states_ent _ _ _ _ _ _ _ _ _ R U NEk S)
        as [[Y _] | [[Y _] | [[_ Y] | [m1 [Y _]]]]]; ent_state_comp Y;
        first [pending_disj BP Y | pending_disj X Y].
    + (* the overlap entered them from dormant, by reading the next mode *)
      destruct OV as [EQ | [b B2]]; [subst p2'; contradiction | ].
      destruct (pendingOvlp_prev _ _ _ OS B2 X) as [BP | [_ [v Eb]]]; [contradiction | ].
      assert (ACT : forall b0, p2 -PA- b0 -PA> p2' -> entChanAct b0).
      { intros b0 B0. destruct (pendingOvlp_prev _ _ _ OS B0 X) as [BP | [_ [v0 E0]]];
          [contradiction | subst b0; left; reflexivity]. }
      destruct (triple_disc_ent_chan 1 R S eq_refl eq_refl ACT) as [EQ | S2];
        [subst p2'; contradiction | ].
      destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S2) as [EQ | [c [T2 [_ [_ NX]]]]];
        [subst p2'; contradiction | ].
      destruct (pendingOvlp_prev _ _ _ OS T2 X) as [BP | [_ [v0 E0]]]; [contradiction | ].
      subst c. destruct (NX v0 eq_refl) as [NM Ek]. subst k'.
      exact (nextMode_unstable _ _ NM).
  - (* a delay: the overlap was in one of these states, and a transition stays a transition *)
    destruct e as [p l h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    ent_state_destr X p1' p2' p3' l' h' k'. cbv beta in X.
    lets T : triple_del_ent S. destruct T as [_ [D2 _]].
    assert (U : unstable k)
      by (apply IH; constructor; constructor; exact (pendingOvlp_del_bkwd _ _ _ OS D2 X)).
    simpl. inversion U; subst. lets K : link_ent_mState_del S.
    destruct (delMStatePresTrans _ _ _ _ _ K) as [t' Et']. subst. constructor.
Qed.

Lemma ovAbort_unstable e : reachableProtEnt e -> ovAbortStateEnt e -> unstable (mstEnt e).  
  (*Proof: Use some general inter-component tactics- at least pre-tactics anyway.*)
Proof.
  intros R A. apply (pendingOvlp_unstable_ent _ R). ent_state_destr A p1 p2 p3 l h k.
  constructor; constructor. cbv beta. do 3 right. exact A.
Qed.

(** In a reachable entity with an unstable mode state, a step that changes the mode state
leaves the overlap component outside the nextSince states: it has just switched mode, from
switchCurr or tfsCurr, or aborted, from ovAbort or tfsNext (mState_switch_states_ent).*)
Lemma mState_change_not_nextSince_ent p l h k p' l' h' k' a :
  reachableProtEnt ([|p, l, h, k|]) -> unstable k -> k <> k' ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  ~ nextSinceStateEnt ([|p', l', h', k'|]).
Proof.
  intros R U NE S NS.
  destruct (mState_switch_states_ent _ _ _ _ _ _ _ _ _ R U NE S)
    as [[_ D] | [[_ D] | [[_ D] | [m [_ D]]]]];
    ent_state_comp D; ent_state_comp NS;
    destruct NS as [m1 t1 x1 y1 X | m1 t1 l1 X | m1 X | m1 X];
    prot_outProc_in_not_unfold;
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ D) X) as BT;
    prot_outProc_in_not_body; try unfold liftVarList in BT; refute_by_chan BT.
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
      * assert (ACT : forall b0, p2 -PA- b0 -PA> p2' -> entChanAct b0).
        { intros b0 B0. destruct (tfsNext_next_act _ _ _ _ B0 TN) as [[Eb _] | [Eb _]];
            subst b0; right; reflexivity. }
        destruct (triple_disc_ent_chan 1 R S eq_refl eq_refl ACT) as [EQ | S2];
          [subst p2'; exfalso; ov_disj TN X | ].
        destruct (ent_disc_proc_write _ _ _ _ _ _ _ _ _ S2) as [EQ | [c [T2 [_ [_ CN]]]]];
          [subst p2'; exfalso; ov_disj TN X | ].
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
        assert (ACT : forall b0, p2 -PA- b0 -PA> p2' -> entChanAct b0).
        { intros b0 B0. destruct (tfsCurr_next_act _ _ _ B0 TC) as [[Eb _] | Y];
            [subst b0; right; reflexivity | exfalso; ov_disj Y X]. }
        destruct (triple_disc_ent_chan 1 R S eq_refl eq_refl ACT) as [EQ | S2];
          [subst p2'; exfalso; ov_disj TC X | ].
        destruct (ent_disc_proc_write _ _ _ _ _ _ _ _ _ S2) as [EQ | [c [T2 [CC _]]]];
          [subst p2'; exfalso; ov_disj TC X | ].
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
      assert (NE : p2 <> p2').
      { intro EQ. subst p2'. pose proof (bisim_trans _ _ _ (bisim_symm _ _ TSE) TN) as BT.
        prot_outProc_in_not_body. refute_by_chan BT. }
      assert (ACT : forall b, p2 -PA- b -PA> p2' -> entChanAct b).
      { intros b B. destruct (tfsStart_next_act _ _ _ B TSE) as [v [Eb _]]. subst b.
        left. reflexivity. }
      destruct (triple_disc_ent_chan 1 R S eq_refl eq_refl ACT) as [EQ | S2];
        [contradiction | ].
      destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S2) as [EQ | [c [T2 [_ [CR _]]]]];
        [contradiction | ].
      destruct (tfsStart_next_act _ _ _ T2 TSE) as [v [Ec TN']]. subst c.
      destruct (CR v eq_refl) as [Ev Ek]. subst v k'.
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

(** A time whose expression evaluates to zero is zero.*)
Local Lemma liftTimeExp_zero_inv (t : Time) : evalExpFunTime (liftTimeExp t) = Some zeroTime ->
  t = zeroTime.
Proof. unfold liftTimeExp. rewrite evalExpFunTime_time. congruence. Qed.

(** An ovWait whose timers are times steps into ovReady only by reading its position, once its
position timer has run out, and keeps its mode and first parameter. It steps into switchBc only
by pausing, once its pause timer has run out.*)
Local Lemma ovWait_time_step_ovReady (m : Mode) (t x y : Time) b q :
  ovWait m t x y -PA- b -PA> q -> (exists m' u l', q ~p~ ovReady m' u l') ->
  y = zeroTime /\ exists (l : Position), q ~p~ ovReady m t l.
Proof.
  intros T [m' [u [l' B]]]. unfold ovWait in T. invert_disc_prefixes; explicit_typed_input;
    clean_proc_hyp B;
    try solve [exfalso; unfold_app_hyp_l B; prot_outProc_in_not_body;
               unfold liftNameProc, liftVarList in B; refute_by_chan B].
  split; [apply liftTimeExp_zero_inv; assumption | ].
  eexists. unfold_app_bisim. apply bisim_refl.
Qed.

Local Lemma ovWait_time_step_switchBc (m : Mode) (t x y : Time) b q :
  ovWait m t x y -PA- b -PA> q -> (exists m', q ~p~ switchBc m') -> x = zeroTime.
Proof.
  intros T [m' B]. unfold ovWait in T. invert_disc_prefixes; explicit_typed_input;
    clean_proc_hyp B;
    try solve [exfalso; unfold_app_hyp_l B; prot_outProc_in_not_body;
               unfold liftNameProc, liftVarList in B; refute_by_chan B].
  apply liftTimeExp_zero_inv; assumption.
Qed.

(** init reads a current mode v and starts ovWait with the wait time from v to its mode, plus the
period, as its first parameter and pause timer, and zero as its position timer.*)
Local Lemma init_time_step (m1 : Mode) b q : init m1 -PA- b -PA> q ->
  exists (v : Mode), b = chanMCurrRead ;? [baseMode v] /\
  q ~p~ ovWait m1 (eAdd (eWaitTime v m1) (ePeriod m1)) (eAdd (eWaitTime v m1) (ePeriod m1))
    zeroTime.
Proof.
  intro T. unfold init in T. invert_disc_prefixes; explicit_typed_input.
  eexists. split; [reflexivity | ]. clean_proc. unfold_app_bisim. apply bisim_refl.
Qed.

(** A delay keeps the overlap component waiting for the same mode and wait time, and takes at
most the delay off its two timers.*)
Local Lemma ovWait_del_pres_bound m t x y p p' d :
  ovWaitState m t x y p -> p -PD- d -PD> p' ->
  exists x' y', ovWaitState m t x' y' p' /\ (x - d <= x')%R /\ (y - d <= y')%R.
Proof.
  intros U V. destruct (bisim_step_del _ _ _ _ U V) as [q [W B]].
  unfold ovWait in W.
  repeat match goal with
    | [H : _ $+$ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    | [H : _ $< _ >$ ? _ -PD- _ -PD> _ |- _] => apply del_self_inPrefix in H; subst
    end.
  match goal with [HC : $< _ >$ (_ $< _ >$ ? _) -PD- _ -PD> _ |- _] =>
    destruct (del_del_bisim_bound _ _ _ _ _ (evalExpFunTime_time _) (del_self_inPrefix _ _ _) HC)
    as [y' [BC Ly]] end.
  match goal with [HD : $< _ >$ (_ $< _ >$ ! _) -PD- _ -PD> _ |- _] =>
    destruct (del_del_bisim_bound _ _ _ _ _ (evalExpFunTime_time _) (del_self_outPrefix _ _ _) HD)
    as [x' [BD Lx]] end.
  exists x' y'. split; [ | split; assumption]. unfold ovWaitState, ovWait.
  eapply bisim_trans; [exact B | ].
  repeat apply choice_bisim_context; first [apply bisim_refl | assumption].
Qed.

(** The wait init sets for a change from m0 to m1 evaluates to a time, which less the period of
m1 is at least the time the change takes.*)
Local Lemma waitTime_period_eval (m0 m1 : Mode) (P : m0 -mtr-> m1) :
  exists (T : Time), evalExpFunTime (eAdd (eWaitTime m0 m1) (ePeriod m1)) = Some T /\
    (modeTransTime m0 m1 P <= T -nn- period m1)%R /\ (T -nn- period m1 <= T)%R.
Proof.
  assert (EV : evalExpFunTime (eAdd (eWaitTime m0 m1) (ePeriod m1)) =
    Some (mkTime (time (waitTime m0 m1 P) +nn+ time (period m1)))).
  { unfold evalExpFunTime. cbn [evalExpFun]. unfold modeTransRelOpt.
    destruct (modeTransRelDec m0 m1) as [P' | N]; [ | contradiction].
    assert (E : P' = P) by apply proof_irrelevance. subst P'.
    cbn [decToOption option_map].
    destruct (waitTime m0 m1 P) as [w]. destruct (period m1) as [per]. reflexivity. }
  exists (mkTime (time (waitTime m0 m1 P) +nn+ time (period m1))). split.
  - exact EV.
  - assert (RM : (modeTransTime m0 m1 P <= waitTime m0 m1 P)%R).
    { unfold waitTime. rewrite timeMax_RMax. apply Rmax_l. }
    remember (waitTime m0 m1 P) as w eqn:Ew. remember (period m1) as per eqn:Ep.
    change (time (mkTime (time w +nn+ time per))) with (time w +nn+ time per).
    pose proof (cond_nonneg (time w)). pose proof (cond_nonneg (time per)).
    rewrite subNonnegTot_le_Rminus_eq by (rewrite addNonnegFact; lra).
    rewrite addNonnegFact. split; lra.
Qed.

(** Proves k' = k for a step S of a reachable entity R whose mode state k is unstable (U), from
X : p2 ~p~ Y for an overlap state Y that writes nothing on the mode state.*)
Local Ltac mState_stays_tac R U S X :=
  apply (mState_stays_ent _ _ _ _ _ _ _ _ _ _ _ _ _ R U S);
  let Y := fresh "Y" in first [intros ? Y | intros Y]; ov_states_disj X Y.

(** Bounds on the mode state's transition timer in a reachable entity: a mode change never has
longer left than it takes, and while the overlap component waits for its mode switch the timer
is within ovWait's pause timer and the wait it has left, and within ovReady's, and has run out
in switchBc and switchCurr. In init the mode state changes to init's mode.*)
Lemma transTimer_bound_ent (e : Entity) : reachableProtEnt e ->
  forall p1 p2 p3 l h k, e = [|p1 $||$ p2 $||$ p3, l, h, k|] ->
  (forall m0 m1 tau, k = <| m0, m1, tau |> ->
     exists (P : m0 -mtr-> m1), (tau <= modeTransTime m0 m1 P)%R) /\
  ((exists (m : Mode), initState m p2) ->
     exists m1 m0 tau, initState m1 p2 /\ k = <| m0, m1, tau |>) /\
  ((exists m t x y, ovWaitStateExp m t x y p2) ->
     exists (m1 : Mode) (t1 x1 y1 : Time) (m0 m' : Mode) (tau : Time),
     ovWaitState m1 t1 x1 y1 p2 /\ k = <| m0, m', tau |> /\ (tau <= x1)%R /\
     (tau <= (t1 -nn- period m1) + y1)%R) /\
  ((exists m t l0, ovReadyStateExp m t l0 p2) ->
     exists (m1 : Mode) (t1 : Time) (l1 : Position) (m0 m' : Mode) (tau : Time),
     ovReadyState m1 t1 l1 p2 /\ k = <| m0, m', tau |> /\ (tau <= t1 -nn- period m1)%R) /\
  ((exists (m : Mode), switchBcState m p2) -> exists m0 m', k = <| m0, m', zeroTime |>) /\
  (switchCurrState p2 -> exists m0 m', k = <| m0, m', zeroTime |>).
Proof.
  intro R. induction R as [e I | e e' a R IH S | e e' d R IH S]; intros q1 q2 q3 l0 h0 k0 E.
  - (* initial: the overlap is dormant and the mode state stable *)
    subst e. inversion I; subst.
    split; [intros ? ? ? EQ; discriminate | ].
    repeat split.
    + intros [m0 X]. exfalso. pose proof (bisim_refl dormant) as D. ov_states_disj D X.
    + intros [m0 [t [x [y X]]]]. exfalso. pose proof (bisim_refl dormant) as D.
      ov_states_disj D X.
    + intros [m0 [t [l1 X]]]. exfalso. pose proof (bisim_refl dormant) as D.
      ov_states_disj D X.
    + intros [m0 X]. exfalso. pose proof (bisim_refl dormant) as D. ov_states_disj D X.
    + intros X. exfalso. pose proof (bisim_refl dormant) as D. ov_states_disj D X.
  - (* a discrete step *)
    subst e'. destruct e as [p l h k].
    lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    destruct (IH p1 p2 p3 l h k eq_refl) as [I0 [I1 [I2 [I3 [I4 I5]]]]]. clear IH.
    lets OV : triple_disc_ent S. destruct OV as [_ [OV _]].
    (* the bound on a mode change under way survives any step of the mode state *)
    split.
    { destruct (ent_disc_mState _ _ _ _ _ _ _ _ _ S) as [EQ | [am K]];
        [subst k0; exact I0 | exact (mState_trans_bound_step _ _ _ K I0)]. }
    repeat split.
    + (* init: the overlap was init already, or was dormant and read the next mode *)
      intros [m X]. destruct OV as [EQ | [b B2]].
      * subst q2. destruct (I1 (ex_intro _ m X)) as [m1 [m0 [tau [X1 Ek]]]].
        assert (U : unstable k) by (subst k; constructor).
        assert (Ek0 : k0 = k) by (mState_stays_tac R U S X1).
        subst k0. exists m1 m0 tau. split; assumption.
      * assert (ACT : forall b0, p2 -PA- b0 -PA> q2 -> entChanAct b0).
        { intros b0 B0. destruct (init_prev _ _ _ _ B0 OS X) as [_ Eb]. subst b0.
          left. reflexivity. }
        destruct (init_prev _ _ _ _ B2 OS X) as [D _].
        destruct (triple_disc_ent_chan 1 R S eq_refl eq_refl ACT) as [EQ | S2];
          [subst q2; exfalso; ov_states_disj D X | ].
        destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S2) as [EQ | [c [T2 [_ [_ NX]]]]];
          [subst q2; exfalso; ov_states_disj D X | ].
        destruct (init_prev _ _ _ _ T2 OS X) as [_ Ec]. subst c.
        destruct (NX m eq_refl) as [NM Ek]. subst k0.
        destruct k as [m2 | m0 m2 tau]; [discriminate NM | ]. injection NM as NM. subst m2.
        exists m m0 tau. split; [exact X | reflexivity].
    + (* ovWait: the overlap was ovWait already, or was init and read the current mode, or was
         ovReady and broadcast *)
      intros XW. destruct OV as [EQ | [b B2]].
      * subst q2. destruct (I2 XW) as [m1 [t1 [x1 [y1 [m0 [m' [tau [X1 [Ek [L1 L2]]]]]]]]]].
        assert (U : unstable k) by (subst k; constructor).
        assert (Ek0 : k0 = k) by (mState_stays_tac R U S X1).
        subst k0. exists m1 t1 x1 y1 m0 m' tau.
        split; [exact X1 | split; [exact Ek | split; [exact L1 | exact L2]]].
      * destruct XW as [mw [tw [xw [yw XW]]]].
        destruct (ovWaitExp_prev _ _ _ _ _ _ _ B2 OS XW) as [_ [XI | [u [lr XR]]]].
        -- destruct (I1 (ex_intro _ mw XI)) as [m1 [m0 [tau [X1 Ek]]]].
           destruct (I0 _ _ _ Ek) as [P HP].
           assert (ACT : forall b0, p2 -PA- b0 -PA> q2 -> entChanAct b0).
           { intros b0 B0. destruct (bisim_step_disc _ _ _ _ X1 B0) as [r [TR _]].
             destruct (init_time_step _ _ _ TR) as [v [Eb _]]. subst b0. left. reflexivity. }
           destruct (triple_disc_ent_chan 1 R S eq_refl eq_refl ACT) as [EQ | S2];
             [subst q2; exfalso; ov_states_disj X1 XW | ].
           destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S2) as [EQ | [c [T2 [_ [CR _]]]]];
             [subst q2; exfalso; ov_states_disj X1 XW | ].
           destruct (bisim_step_disc _ _ _ _ X1 T2) as [r [TR BR]].
           destruct (init_time_step _ _ _ TR) as [v [Ec BV]]. subst c.
           destruct (CR v eq_refl) as [Ev Ek0]. subst k0 k. simpl in Ev. subst v.
           destruct (waitTime_period_eval m0 m1 P) as [T [ET [LT1 LT2]]].
           exists m1 T T zeroTime m0 m1 tau. split; [ | split; [reflexivity | ]].
           ++ eapply (ovWaitStateExp_time m1 _ _ _ T T zeroTime);
                [exact ET | exact ET | apply evalExpFunTime_time | ].
              red. eapply bisim_trans; [exact BR | exact BV].
           ++ simpl. split; lra.
        -- assert (XR' : exists m t l0, ovReadyStateExp m t l0 p2) by (do 3 eexists; exact XR).
           destruct (I3 XR') as [m1 [t1 [l1 [m0 [m' [tau [X1 [Ek L1]]]]]]]].
           destruct (bisim_step_disc _ _ _ _ X1 B2) as [r [TR BR]].
           destruct (ovReady_step_ovWait _ _ _ _ _ TR) as [_ BV].
           assert (U : unstable k) by (subst k; constructor).
           assert (Ek0 : k0 = k) by (mState_stays_tac R U S X1).
           subst k0. exists m1 (mkTime (time t1 -nn- time (period m1)))
             (mkTime (time t1 -nn- time (period m1))) (period m1) m0 m' tau.
           split; [ | split; [exact Ek | ]].
           ++ eapply (ovWaitStateExp_time m1 _ _ _ (mkTime (time t1 -nn- time (period m1)))
                (mkTime (time t1 -nn- time (period m1))) (period m1));
                [apply evalExpFunTime_subtract_period; apply evalExpFunTime_time
                | apply evalExpFunTime_subtract_period; apply evalExpFunTime_time
                | apply evalExpFunTime_period | ].
              red. eapply bisim_trans; [exact BR | exact BV].
           ++ simpl. split; [exact L1 | ].
              pose proof (subNonnegTot_le_Rminus (time t1 -nn- time (period m1))
                (time (period m1))). lra.
    + (* ovReady: the overlap was ovReady already, or was ovWait and read its position *)
      intros XR. destruct OV as [EQ | [b B2]].
      * subst q2. destruct (I3 XR) as [m1 [t1 [l1 [m0 [m' [tau [X1 [Ek L1]]]]]]]].
        assert (U : unstable k) by (subst k; constructor).
        assert (Ek0 : k0 = k) by (mState_stays_tac R U S X1).
        subst k0. exists m1 t1 l1 m0 m' tau. split; [exact X1 | split; [exact Ek | exact L1]].
      * destruct XR as [mr [tr [lr XR]]].
        destruct (ovReadyExp_prev _ _ _ _ _ _ B2 OS XR) as [e2 [e3 [e4 XW0]]].
        assert (XW : exists m t x y, ovWaitStateExp m t x y p2) by (do 4 eexists; exact XW0).
        destruct (I2 XW) as [m1 [t1 [x1 [y1 [m0 [m' [tau [X1 [Ek [L1 L2]]]]]]]]]].
        destruct (bisim_step_disc _ _ _ _ X1 B2) as [r [TR BR]].
        assert (XR' : exists m' u l', r ~p~ ovReady m' u l')
          by (do 3 eexists; exact (bisim_trans _ _ _ (bisim_symm _ _ BR) XR)).
        destruct (ovWait_time_step_ovReady _ _ _ _ _ _ TR XR') as [Ey [l2 BV]]. subst y1.
        assert (U : unstable k) by (subst k; constructor).
        assert (Ek0 : k0 = k) by (mState_stays_tac R U S X1).
        subst k0. exists m1 t1 l2 m0 m' tau. split; [ | split; [exact Ek | ]].
        -- red. eapply bisim_trans; [exact BR | exact BV].
        -- simpl in L2. lra.
    + (* switchBc: the overlap was switchBc already, or was ovWait and paused, which its timer
         allows only once the mode state's has run out *)
      intros [m X]. destruct OV as [EQ | [b B2]].
      * subst q2. destruct (I4 (ex_intro _ m X)) as [m0 [m' Ek]].
        assert (U : unstable k) by (subst k; constructor).
        assert (Ek0 : k0 = k) by (mState_stays_tac R U S X).
        subst k0. exists m0 m'. exact Ek.
      * destruct (switchBc_prev _ _ _ _ B2 OS X) as [t [y XW]].
        assert (XW' : exists m t x y, ovWaitStateExp m t x y p2) by (do 4 eexists; exact XW).
        destruct (I2 XW') as [m1 [t1 [x1 [y1 [m0 [m' [tau [X1 [Ek [L1 L2]]]]]]]]]].
        destruct (bisim_step_disc _ _ _ _ X1 B2) as [r [TR BR]].
        assert (XB : exists m', r ~p~ switchBc m')
          by (eexists; exact (bisim_trans _ _ _ (bisim_symm _ _ BR) X)).
        lets Ex : ovWait_time_step_switchBc TR XB. subst x1.
        assert (U : unstable k) by (subst k; constructor).
        assert (Ek0 : k0 = k) by (mState_stays_tac R U S X1).
        subst k0 k. exists m0 m'. f_equal. apply timeEqR. simpl in L1.
        pose proof (cond_nonneg (time tau)). simpl. lra.
    + (* switchCurr: the overlap was switchCurr already, or was switchBc and woke the
         broadcaster *)
      intros X. destruct OV as [EQ | [b B2]].
      * subst q2. destruct (I5 X) as [m0 [m' Ek]]. exists m0 m'.
        destruct (eqDecModeState k k0) as [Ek0 | NE]; [subst k0; exact Ek | exfalso].
        assert (U : unstable k) by (subst k; constructor).
        destruct (mState_switch_states_ent _ _ _ _ _ _ _ _ _ R U NE S)
          as [[Y _] | [[_ Y] | [[Y _] | [m1 [Y _]]]]]; ent_state_comp Y; ov_states_disj X Y.
      * destruct (switchCurr_prev _ _ _ B2 OS X) as [m XB].
        destruct (I4 (ex_intro _ m XB)) as [m0 [m' Ek]].
        assert (U : unstable k) by (subst k; constructor).
        assert (Ek0 : k0 = k) by (mState_stays_tac R U S XB).
        subst k0. exists m0 m'. exact Ek.
  - (* a delay: the overlap stays in its state, and ovWait's timers count down as the mode
       state's does *)
    subst e'. destruct e as [p l h k].
    lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    destruct (IH p1 p2 p3 l h k eq_refl) as [I0 [I1 [I2 [I3 [I4 I5]]]]]. clear IH.
    lets T : triple_del_ent S. destruct T as [_ [D2 _]].
    lets K : link_ent_mState_del S.
    split; [exact (mState_trans_bound_step _ _ _ K I0) | ].
    repeat split.
    + intros [m X].
      assert (X0 : initState m p2).
      { red. apply (overlap_del_bkwd (init m) _ _ _ OS D2 X).
        intros m2 e2 e3 e4 B. ovWait_bisim_contra B. }
      destruct (I1 (ex_intro _ m X0)) as [m1 [m0 [tau [X1 Ek]]]]. subst k.
      destruct (delMStatePresTrans _ _ _ _ _ K) as [tau' Ek0]. subst k0.
      exists m1 m0 tau'. split; [ | reflexivity].
      red. eapply bisim_del_pres; [del_self_body | exact X1 | exact D2].
    + intros [m [t [x [y X]]]].
      destruct (ovWait_del_bkwd _ _ _ _ _ _ _ OS D2 X) as [m2 [t2 [x2 [y2 [X0 _]]]]].
      assert (XW : exists m t x y, ovWaitStateExp m t x y p2) by (do 4 eexists; exact X0).
      destruct (I2 XW) as [m1 [t1 [x1 [y1 [m0 [m' [tau [X1 [Ek [L1 L2]]]]]]]]]].
      destruct (ovWait_del_pres_bound _ _ _ _ _ _ _ X1 D2) as [x1' [y1' [X1' [Lx Ly]]]].
      subst k. destruct (delMStatePresTrans _ _ _ _ _ K) as [tau' Ek0]. subst k0.
      exists m1 t1 x1' y1' m0 m' tau'. split; [exact X1' | split; [reflexivity | ]].
      pose proof (cond_nonneg (time x1')). pose proof (cond_nonneg (time y1')).
      pose proof (cond_nonneg (time t1 -nn- time (period m1))).
      destruct (delMStateTrans _ _ _ _ _ _ _ K) as [[Et Lt] | Et].
      * subst tau'. simpl. split; lra.
      * subst tau. simpl in L1, L2. split; lra.
    + intros [m [t [l1 X]]].
      assert (X0 : ovReadyStateExp m t l1 p2).
      { red. apply (overlap_del_bkwd (ovReady m t l1) _ _ _ OS D2 X).
        intros m2 e2 e3 e4 B. ovWait_bisim_contra B. }
      assert (XR : exists m t l0, ovReadyStateExp m t l0 p2) by (do 3 eexists; exact X0).
      destruct (I3 XR) as [m1 [t1 [l2 [m0 [m' [tau [X1 [Ek L1]]]]]]]].
      subst k. destruct (delMStatePresTrans _ _ _ _ _ K) as [tau' Ek0]. subst k0.
      exists m1 t1 l2 m0 m' tau'. split; [ | split; [reflexivity | ]].
      * red. eapply bisim_del_pres; [del_self_body | exact X1 | exact D2].
      * destruct (delMStateTrans _ _ _ _ _ _ _ K) as [[Et Lt] | Et].
        -- subst tau'. simpl. apply cond_nonneg.
        -- subst tau. simpl in L1. pose proof (cond_pos (delay d)). lra.
    + intros [m X].
      assert (X0 : switchBcState m p2).
      { red. apply (overlap_del_bkwd (switchBc m) _ _ _ OS D2 X).
        intros m2 e2 e3 e4 B. ovWait_bisim_contra B. }
      destruct (I4 (ex_intro _ m X0)) as [m0 [m' Ek]]. subst k.
      exists m0 m'. exact (delMStateTout _ _ _ _ K).
    + intros X.
      assert (X0 : switchCurrState p2).
      { red. apply (overlap_del_bkwd switchCurr _ _ _ OS D2 X).
        intros m2 e2 e3 e4 B. ovWait_bisim_contra B. }
      destruct (I5 X0) as [m0 [m' Ek]]. subst k.
      exists m0 m'. exact (delMStateTout _ _ _ _ K).
Qed.

(**If we're in the state switchCurr m', then the next mode is m'.
Corollary: switchCurr is urgent.*)
Theorem switchCurr_mState (e : Entity) :
  reachableProtEnt e -> switchCurrStateEnt e -> exists m m',
  mstEnt e = <| m, m', zeroTime |>.
Proof.
  intros R SC. destruct e as [p l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  ent_state_comp SC.
  destruct (transTimer_bound_ent _ R p1 p2 p3 l h k eq_refl) as [_ [_ [_ [_ [_ I5]]]]].
  exact (I5 SC).
Qed.
(**Proof: Inductgion on reachabledEnt.
Relies on a chain of support of similar results for switchBc, ovWait,
ovReady and init. Each one relying on the last. The ovWait and ovReady ones
would need to be proved by mutual induction.*)

(** The listener becomes paused only by taking chanPause.*)
Local Lemma paused_prev_act p p' b : listenerState p -> p -PA- b -PA> p' -> pausedState p' ->
  b = chanPause *?.
Proof.
  intros LS T P. red in P.
  destruct (listenerState_shape _ LS) as [H | m H | H | m H | H | m l H | m e H | m e H | H | H];
    shape_step_pre B; try reflexivity;
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ P) B) as BT; clear B P;
    unfold liftNameProc in BT;
    first [ prot_outProc_in_not_body; refute_by_chan BT
          | unfold_app_hyp BT; first [ prot_outProc_in_not_body; refute_by_chan BT
              | resolve_cond BT; unfold liftNameProc in BT; try unfold_app_hyp BT;
                prot_outProc_in_not_body; refute_by_chan BT ] ].
Qed.

(** A paused listener only takes chanUnpause, after which it is listening.*)
Local Lemma paused_next_act p p' b : pausedState p -> p -PA- b -PA> p' ->
  b = chanUnpause *? /\ listeningState p'.
Proof.
  intros P T. red in P. shape_step_pre B. split; [reflexivity | ].
  red. eapply bisim_trans; [exact B | ]. unfold liftNameProc. unfold_app_bisim. apply bisim_refl.
Qed.

(** A listener that takes chanPause is paused, and one that takes chanUnpause is listening.*)
Local Lemma listener_pause_to_paused p p' : listenerState p -> p -PA- chanPause *? -PA> p' ->
  pausedState p'.
Proof.
  intros LS T.
  destruct (listenerState_shape _ LS) as [H | m H | H | m H | H | m l H | m e H | m e H | H | H];
    shape_step_pre B.
  red. eapply bisim_trans; [exact B | ]. unfold liftNameProc. unfold_app_bisim. apply bisim_refl.
Qed.

Local Lemma listener_unpause_to_listening p p' : listenerState p -> p -PA- chanUnpause *? -PA> p' ->
  listeningState p'.
Proof.
  intros LS T.
  destruct (listenerState_shape _ LS) as [H | m H | H | m H | H | m l H | m e H | m e H | H | H];
    shape_step_pre B;
  red; eapply bisim_trans; try exact B; unfold liftNameProc; unfold_app_bisim; apply bisim_refl.
Qed.

(** The overlap component enters a switch state only by its output on chanPause, and leaves the
switch states only by its output on chanUnpause.*)
Local Lemma switch_prev_act p p' b : overlapState p -> p -PA- b -PA> p' -> switchState p' ->
  switchState p \/ b = chanPause *!.
Proof.
  intros O TR SW. destruct SW as [m SP | SP | SP]; red in SP; backtrack_shape SP;
    output_values;
    first [ right; reflexivity | left; eapply switBcSt; exact B | left; apply switCurSt; exact B ].
Qed.

Local Lemma switch_next_act p p' b : switchState p -> p -PA- b -PA> p' ->
  switchState p' \/ b = chanUnpause *!.
Proof.
  intros SW TR. destruct SW as [m SP | SP | SP]; red in SP;
    destruct (bisim_step_disc _ _ _ _ SP TR) as [q [TQ BQ]];
    prot_outProc_in_not_body; invert_disc_prefixes; output_values; clean_proc_hyp BQ;
    unfold liftNameProc in BQ;
    first [ right; reflexivity
          | left; apply switCurSt; red; eapply bisim_trans; [exact BQ | ];
            unfold_app_bisim; apply bisim_refl
          | left; apply switLisSt; red; eapply bisim_trans; [exact BQ | ];
            unfold_app_bisim; apply bisim_refl ].
Qed.

(** The overlap component's output on chanPause leads to a switch state, and its output on
chanUnpause to dormant.*)
Local Lemma overlap_pause_to_switch p p' : overlapState p -> p -PA- chanPause *! -PA> p' ->
  switchState p'.
Proof.
  intros O TR.
  destruct (overlapState_shape _ O)
    as [B | m B | m e2 e3 e4 B | m e2 l B | m B | B | B | B | B | m B | B | B | B];
    destruct (bisim_step_disc _ _ _ _ B TR) as [q [TQ BQ]];
    prot_outProc_in_not_body; invert_disc_prefixes; output_values; clean_proc_hyp BQ.
  eapply switBcSt. red. eapply bisim_trans; [exact BQ | ]. unfold_app_bisim. apply bisim_refl.
Qed.

Local Lemma overlap_unpause_to_dormant p p' : overlapState p -> p -PA- chanUnpause *! -PA> p' ->
  dormantState p'.
Proof.
  intros O TR.
  destruct (overlapState_shape _ O)
    as [B | m B | m e2 e3 e4 B | m e2 l B | m B | B | B | B | B | m B | B | B | B];
    destruct (bisim_step_disc _ _ _ _ B TR) as [q [TQ BQ]];
    prot_outProc_in_not_body; invert_disc_prefixes; output_values; clean_proc_hyp BQ;
    red; eapply bisim_trans; try exact BQ; unfold liftNameProc; unfold_app_bisim; apply bisim_refl.
Qed.

(** The broadcaster takes neither chanPause nor chanUnpause.*)
Local Lemma broadcast_pause_in_not p p' : broadcastState p -> p -PA- chanPause *? -PA> p' ->
  False.
Proof. intros S T. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra. Qed.

Local Lemma broadcast_unpause_in_not p p' : broadcastState p ->
  p -PA- chanUnpause *? -PA> p' -> False.
Proof. intros S T. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra. Qed.

(** A step of the overlap component keeps it in or out of the switch states, unless it is an
output on chanPause or chanUnpause. Likewise for the listener and paused, with inputs.*)
Local Lemma overlap_switch_status p p' b : overlapState p -> p -PA- b -PA> p' ->
  (switchState p' <-> switchState p) \/ b = chanPause *! \/ b = chanUnpause *!.
Proof.
  intros O T. destruct (Classical_Prop.classic (switchState p)) as [SW | NSW].
  - destruct (switch_next_act _ _ _ SW T) as [SW' | U]; [left; tauto | right; right; exact U].
  - destruct (Classical_Prop.classic (switchState p')) as [SW' | NSW'].
    + destruct (switch_prev_act _ _ _ O T SW') as [SW | P]; [contradiction | right; left; exact P].
    + left. tauto.
Qed.

Local Lemma listener_paused_status p p' b : listenerState p -> p -PA- b -PA> p' ->
  (pausedState p' <-> pausedState p) \/ b = chanPause *? \/ b = chanUnpause *?.
Proof.
  intros LS T. destruct (Classical_Prop.classic (pausedState p)) as [P | NP].
  - destruct (paused_next_act _ _ _ P T) as [U _]. right; right; exact U.
  - destruct (Classical_Prop.classic (pausedState p')) as [P' | NP'].
    + right; left. eapply paused_prev_act; eassumption.
    + left. tauto.
Qed.

(** A listening listener is not paused, and a dormant overlap component is in no switch
state.*)
Local Lemma listening_not_paused p : listeningState p -> pausedState p -> False.
Proof.
  intros L P. red in L, P. pose proof (bisim_trans _ _ _ (bisim_symm _ _ L) P) as BT.
  prot_outProc_in_not_body. refute_by_chan BT.
Qed.

Local Lemma dormant_not_switch p : dormantState p -> switchState p -> False.
Proof.
  intros D SW. red in D. destruct SW as [m SP | SP | SP]; red in SP;
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ D) SP) as BT;
    prot_outProc_in_not_body; refute_by_chan BT.
Qed.

(** A listener state delays only to a bisimilar state.*)
Local Lemma listener_del_bisim p p' d : listenerState p -> p -PD- d -PD> p' -> p ~p~ p'.
Proof.
  intros LS D.
  destruct (listenerState_shape _ LS) as [H | m H | H | m H | H | m l H | m e H | m e H | H | H];
    (eapply bisim_trans; [exact H | ]; apply bisim_symm;
     eapply bisim_del_pres; [del_self_body | exact H | exact D]).
Qed.

(** A switch state delays only to a switch state, and only a switch state delays into one.*)
Local Lemma switch_del_pres p p' d : switchState p -> p -PD- d -PD> p' -> switchState p'.
Proof.
  intros SW D. destruct SW as [m SP | SP | SP].
  - eapply switBcSt. eapply switchBc_del_pres; eassumption.
  - apply switCurSt. eapply switchCurr_del_pres; eassumption.
  - apply switLisSt. red in SP |- *.
    eapply bisim_del_pres; [del_self_body | exact SP | exact D].
Qed.

Local Lemma switch_del_bkwd p p' d : overlapState p -> p -PD- d -PD> p' -> switchState p' ->
  switchState p.
Proof.
  intros OS D SW. destruct SW as [m SP | SP | SP].
  - eapply switBcSt. red. apply (overlap_del_bkwd (switchBc m) _ _ _ OS D SP).
    intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
  - apply switCurSt. red. apply (overlap_del_bkwd switchCurr _ _ _ OS D SP).
    intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
  - apply switLisSt. red. apply (overlap_del_bkwd switchListen _ _ _ OS D SP).
    intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
Qed.

(** In a reachable entity the listener is paused exactly when the overlap component is in a
switch state.*)
Lemma paused_switch_ent (e : Entity) : reachableProtEnt e ->
  (pausedStateEnt e <-> switchStateEnt e).
Proof.
  intro R. induction R as [e I | e e' a R IH S | e e' d R IH S].
  - (* initial: the listener is listening and the overlap dormant *)
    inversion I; subst. split; intro X; exfalso; ent_state_comp X.
    + eapply listening_not_paused; [apply bisim_refl | exact X].
    + eapply dormant_not_switch; [apply bisim_refl | exact X].
  - destruct e as [p l h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    destruct (triple_disc_ent_fwd _ _ _ _ _ _ _ _ S)
      as [p1' [p2' [p3' [l' [h' [k' [E _]]]]]]].
    subst e'.
    assert (IHc : pausedState p3 <-> switchState p2).
    { split; intro X.
      - assert (Y : switchStateEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]))
          by (apply IH; constructor; constructor; exact X).
        ent_state_comp Y. exact Y.
      - assert (Y : pausedStateEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]))
          by (apply IH; constructor; constructor; exact X).
        ent_state_comp Y. exact Y. }
    cut (pausedState p3' <-> switchState p2').
    { intro G. split; intro X; ent_state_comp X; constructor; constructor; apply G; exact X. }
    destruct (ent_disc_proc_tau_or_chan _ _ _ _ _ _ _ _ _ S) as [EQ | [b [T [Eb | Cb]]]].
    + (* the software stays *)
      inversion EQ; subst. exact IHc.
    + (* a silent step: two components synchronise *)
      subst b.
      destruct (link_reach_triple_tau _ _ _ _ _ _ T PS) as [c [v
        [[T1 [T2 E3]] | [[T1 [T2 E3]] | [[T1 [T3 E2]] | [[T1 [T3 E2]] |
         [[T2 [T3 E1]] | [T2 [T3 E1]]]]]]]]]; subst.
      * (* broadcaster outputs, overlap inputs *)
        destruct (overlap_switch_status _ _ _ OS T2) as [EO | [EP | EU]];
          [rewrite EO; exact IHc | discriminate | discriminate].
      * (* overlap outputs, broadcaster inputs: never on pause or unpause *)
        destruct (overlap_switch_status _ _ _ OS T2) as [EO | [EP | EU]].
        -- rewrite EO; exact IHc.
        -- injection EP as -> ->. exfalso. eapply broadcast_pause_in_not; eassumption.
        -- injection EU as -> ->. exfalso. eapply broadcast_unpause_in_not; eassumption.
      * (* broadcaster outputs, listener inputs: the broadcaster outputs only on outProc *)
        destruct (listener_paused_status _ _ _ LS T3) as [EL | [EP | EU]].
        -- rewrite EL; exact IHc.
        -- injection EP as -> ->. exfalso.
           pose proof (broadcast_out_outProc _ _ _ _ BS T1). discriminate.
        -- injection EU as -> ->. exfalso.
           pose proof (broadcast_out_outProc _ _ _ _ BS T1). discriminate.
      * (* listener outputs, broadcaster inputs *)
        destruct (listener_paused_status _ _ _ LS T3) as [EL | [EP | EU]];
          [rewrite EL; exact IHc | discriminate | discriminate].
      * (* overlap outputs, listener inputs: the pause and the unpause *)
        destruct (listener_paused_status _ _ _ LS T3) as [EL | [EP | EU]].
        -- destruct (overlap_switch_status _ _ _ OS T2) as [EO | [EP | EU]].
           ++ rewrite EL, EO; exact IHc.
           ++ injection EP as -> ->. split; intro.
              ** eapply overlap_pause_to_switch; eassumption.
              ** eapply listener_pause_to_paused; eassumption.
           ++ injection EU as -> ->. split; intro X; exfalso.
              ** eapply listening_not_paused;
                   [eapply listener_unpause_to_listening; eassumption | exact X].
              ** eapply dormant_not_switch;
                   [eapply overlap_unpause_to_dormant; eassumption | exact X].
        -- injection EP as -> ->. split; intro.
           ++ eapply overlap_pause_to_switch; eassumption.
           ++ eapply listener_pause_to_paused; eassumption.
        -- injection EU as -> ->. split; intro X; exfalso.
           ++ eapply listening_not_paused;
                [eapply listener_unpause_to_listening; eassumption | exact X].
           ++ eapply dormant_not_switch; [eapply overlap_unpause_to_dormant; eassumption | exact X].
      * (* listener outputs, overlap inputs *)
        destruct (listener_paused_status _ _ _ LS T3) as [EL | [EP | EU]];
          [ | discriminate | discriminate].
        destruct (overlap_switch_status _ _ _ OS T2) as [EO | [EP | EU]];
          [rewrite EL, EO; exact IHc | discriminate | discriminate].
    + (* a step on one of the entity's channels: one component takes it, and it is not pause
         or unpause *)
      assert (NT : b <> tauAct) by (intro; subst; exact Cb).
      triple_parAll T. apply parAll_disc_nonTau in T; [ | exact NT].
      destruct T as [? [? [? [? T]]]]; triple_pos.
      * exact IHc.
      * match goal with [T2 : p2 -PA- _ -PA> _ |- _] =>
          destruct (overlap_switch_status _ _ _ OS T2) as [EO | [EP | EU]] end;
          [rewrite EO; exact IHc | subst; destruct Cb as [C | C]; discriminate C
          | subst; destruct Cb as [C | C]; discriminate C].
      * match goal with [T3 : p3 -PA- _ -PA> _ |- _] =>
          destruct (listener_paused_status _ _ _ LS T3) as [EL | [EP | EU]] end;
          [rewrite EL; exact IHc | subst; destruct Cb as [C | C]; discriminate C
          | subst; destruct Cb as [C | C]; discriminate C].
  - (* a delay keeps every switch state and the listener as it is *)
    destruct e as [p l h k]. lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
    inversion PS as [p1 p2 p3 BS OS LS]; subst p.
    split; intro X; ent_state_destr X p1' p2' p3' l' h' k';
      lets T : triple_del_ent S; destruct T as [_ [D2 D3]];
      lets B3 : listener_del_bisim LS D3; constructor; constructor.
    + assert (P3 : pausedState p3) by (red; eapply bisim_trans; [exact B3 | exact X]).
      assert (Y : switchStateEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]))
        by (apply IH; constructor; constructor; exact P3).
      ent_state_comp Y. eapply switch_del_pres; eassumption.
    + assert (Y : pausedStateEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]))
        by (apply IH; constructor; constructor; eapply switch_del_bkwd; eassumption).
      ent_state_comp Y. red. eapply bisim_trans; [apply bisim_symm; exact B3 | exact Y].
Qed.

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

(** A delaying entity's software cannot read a position at any point of the delay.*)
Lemma ent_del_pos_sort_not p l h k d e' l0 :
  [|p, l, h, k|] -ED- d ->> e' -> sort (chanPos ;? [basePosition l0]) d p -> False.
Proof.
  intros DEL S. inversion DEL as [d0 p0 p' l1 delta h0 h' k0 k' DP DH DK DM NS]; subst.
  destruct (sort_del _ _ _ S (tae _ _ _ DP)) as [[p'' [d' [DP' [LT DA]]]] | DA].
  - assert (ED : d = d' +d+ minusDelay d d' LT)
      by (rewrite addDelayComm; symmetry; apply minusAddDelay).
    destruct (timeSplit_inter _ _ _ _ _ DH ED) as [h1 [H1 _]].
    destruct (delEnabledMState k d') as [k1 K1].
    destruct (NS (chanPos ;? [basePosition l0])) as [_ NS2].
    destruct (NS2 p'' h1 k1 d' LT DP' H1 K1 DA) as [_ [_ NP]]. apply (NP l0). reflexivity.
  - destruct (NS (chanPos ;? [basePosition l0])) as [NS1 _].
    destruct (NS1 DA) as [_ [_ NP]]. apply (NP l0). reflexivity.
Qed.

(* begin helpers for gotMsgStateEnt_urgent *)
(** A process in the gotMsg state can read any position on the channel pos.*)
Local Lemma gotMsg_pos_in (p : ProcTerm) (m : Mode) (l l0 : Position) :
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
  dae_listener. eapply gotMsg_pos_in. eassumption.
Qed.

(* begin helpers for gotRangeStateEnt_urgent *)
(** A process in the gotRange state can read any mode on the channel mCurr.*)
Local Lemma gotRange_mCurr_in (p : ProcTerm) (m m0 : Mode) (r : Distance) :
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
  eapply gotRange_mCurr_in. eassumption.
Qed.

(* begin helpers for currCompStateEnt_urgent *)
(** A process in the currComp state can input on mStable.*)
Local Lemma currComp_mStable_in (p : ProcTerm) (m : Mode) (r : Distance) :
  currCompState m r p -> discActEnabled p (chanMStableRead *?).
  activation_tac. Qed.

(** A process in the currComp state can input any mode on mNext.*)
Local Lemma currComp_mNext_in (p : ProcTerm) (m m0 : Mode) (r : Distance) :
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
  - dae_listener. eapply currComp_mStable_in. eassumption.
  - intro m0. dae_listener.
    eapply currComp_mNext_in. eassumption.
Qed. (*Relies on the result that the mode state can always
EITHER output on next or stable. #modif-urgent*)

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
  -> False.
Proof.
  intros e e' d R SL DEL. ent_state_destr SL p1 p2 p3 l h k.
  destruct e' as [p' l' h' k']. lets DP : link_ent_soft_del DEL.
  (*We use (paused_switch_ent) to show that the listener component is paused*)
  assert (P : pausedStateEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]))
    by (apply (paused_switch_ent _ R); constructor; constructor; apply switLisSt; exact SL).
  ent_state_comp P.
  (*Now a synchronisation is shown on unpause.*)
  triple_del_sync_not DP (switchListen_unpause_out _ SL) (paused_unpause_in _ P).
Qed.

(** init reads any current mode.*)
Local Lemma init_mCurr_in_shape (m m0 : Mode) p : p ~p~ init m ->
  discActEnabled p (chanMCurrRead ;? [baseMode m0]).
Proof. activation_tac. Qed.

(** The overlap component of a reachable entity that lets time pass is dormant, ovWait, tfsCurr
or tfsListen.*)
Local Lemma delaying_overlap_states p1 p2 p3 l h k e' d :
  reachableProtEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]) ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -ED- d ->> e' ->
  dormantState p2 \/ (exists (m : Mode) (e2 e3 e4 : Exp), p2 ~p~ ovWait m e2 e3 e4) \/
  tfsCurrState p2 \/ tfsListenState p2.
Proof.
  intros R DEL.
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [? ? ? BS OS LS]; subst.
  assert (BSE : broadcastStateEnt ([|p1 $||$ p2 $||$ p3, l, h, k|]))
    by (constructor; constructor; exact BS).
  destruct (overlapState_shape _ OS)
    as [B | m B | m e2 e3 e4 B | m e2 l0 B | m B | B | B | B | B | m B | B | B | B];
    try solve [left; exact B | right; left; do 4 eexists; exact B | right; right; left; exact B
              | right; right; right; exact B];
    exfalso.
  - (* init reads the current mode *)
    eapply ent_del_sync_mState_not; [ | | exact DEL].
    + dae_overlap. apply (init_mCurr_in_shape m (currModeMState k)). exact B.
    + apply modeState_curr_enabled.
  - refine (ovReady_urgent m e2 l0 _ _ _ _ DEL). constructor; constructor; exact B.
  - refine (switchBc_urgent m _ _ _ BSE _ DEL). constructor; constructor; exact B.
  - refine (swithcCurr_urgent (currModeMState k) _ _ _ R _ DEL).
    constructor; constructor; exact B.
  - refine (switchListen_urgent _ _ _ R _ DEL). constructor; constructor; exact B.
  - refine (ovAbort_urgent _ _ _ R _ DEL). constructor; constructor; exact B.
  - refine (tfsStartStateEnt_urgent _ _ _ _ DEL). constructor; constructor; exact B.
  - refine (tfsNext_urgent m _ _ _ R _ DEL). constructor; constructor; exact B.
  - refine (tfsBc_urgent _ _ _ BSE _ DEL). constructor; constructor; exact B.
Qed.

(** The listener in abortOvlp outputs on abort, and ovWait, whatever its timers, takes it.*)
Local Lemma abortOvlp_abort_out p : abortOvlpState p -> discActEnabled p (chanAbort *!).
Proof. activation_tac. Qed.

Local Lemma ovWait_abort_in_shape (m : Mode) (e2 e3 e4 : Exp) p : p ~p~ ovWait m e2 e3 e4 ->
  discActEnabled p (chanAbort *?).
Proof. activation_tac. Qed.

Lemma abortOvlpStateEnt_urgent (e e' : Entity) (d : Delay) :
  reachableProtEnt e -> abortOvlpStateEnt e -> e -ED- d ->> e' -> False.
Proof.
  intros R AO DEL. ent_state_destr AO p1 p2 p3 l h k.
  destruct e' as [p' l' h' k']. lets DP : link_ent_soft_del DEL.
  lets AB : abortOvlp_abort_out AO.
  destruct (delaying_overlap_states _ _ _ _ _ _ _ _ R DEL)
    as [X | [[m [e2 [e3 [e4 X]]]] | [X | X]]].
  - triple_del_sync_not DP (dormant_abort_in _ X) AB.
  - triple_del_sync_not DP (ovWait_abort_in_shape _ _ _ _ _ X) AB.
  - triple_del_sync_not DP (tfsCurr_abort_in _ X) AB.
  - triple_del_sync_not DP (tfsListen_abort_in _ X) AB.
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
    assert (ACT : forall b, p1 -PA- b -PA> p1' -> b = chanPos ;? [basePosition l]) by
      (intros b B; eapply bcReady_prev; eassumption).
    assert (ACT' : forall b, p1 -PA- b -PA> p1' -> entChanAct b)
      by (intros b B; rewrite (ACT b B); left; reflexivity).
    destruct (triple_disc_ent_chan 0 R S eq_refl eq_refl ACT') as [EQ | S1];
      [subst p1'; simpl; apply IH'; exact BR | ].
    destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S1) as [EQ | [c [T [POS _]]]];
      [subst p1'; simpl; apply IH'; exact BR | ].
    simpl. symmetry. exact (POS l (ACT c T)).
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
    assert (ACT : forall b, p2 -PA- b -PA> p2' -> b = chanPos ;? [basePosition l]) by
      (intros b B; eapply ovReady_prev_act; eassumption).
    assert (ACT' : forall b, p2 -PA- b -PA> p2' -> entChanAct b)
      by (intros b B; rewrite (ACT b B); left; reflexivity).
    destruct (triple_disc_ent_chan 1 R S eq_refl eq_refl ACT') as [EQ | S2];
      [subst p2'; simpl; apply IH'; exact OR | ].
    destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S2) as [EQ | [c [T [POS _]]]];
      [subst p2'; simpl; apply IH'; exact OR | ].
    simpl. symmetry. exact (POS l (ACT c T)).
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

(** The listener reads any current mode in rangeBad and gotRange, and stability and any next
mode in currOK and currComp, whatever their ranges.*)
Local Lemma rangeBad_mCurr_in (p : ProcTerm) (m m0 : Mode) :
  rangeBadState m p -> discActEnabled p (chanMCurrRead ;? [baseMode m0]).
Proof. activation_tac. Qed.

Local Lemma gotRange_mCurr_in_shape (p : ProcTerm) (m m0 : Mode) (e : Exp) :
  p ~p~ gotRange m e -> discActEnabled p (chanMCurrRead ;? [baseMode m0]).
Proof. activation_tac. Qed.

Local Lemma currOK_mStable_in (p : ProcTerm) (m : Mode) :
  currOKState m p -> discActEnabled p (chanMStableRead *?).
Proof. activation_tac. Qed.

Local Lemma currOK_mNext_in (p : ProcTerm) (m m0 : Mode) :
  currOKState m p -> discActEnabled p (chanMNextRead ;? [baseMode m0]).
Proof. activation_tac. Qed.

Local Lemma currComp_mStable_in_shape (p : ProcTerm) (m : Mode) (e : Exp) :
  p ~p~ currComp m e -> discActEnabled p (chanMStableRead *?).
Proof. activation_tac. Qed.

Local Lemma currComp_mNext_in_shape (p : ProcTerm) (m m0 : Mode) (e : Exp) :
  p ~p~ currComp m e -> discActEnabled p (chanMNextRead ;? [baseMode m0]).
Proof. activation_tac. Qed.

(**A reachable entity that can delay is in the listening state.*)
Theorem del_listening_pre (e e' : Entity) (d : Delay) :
  reachableProtEnt e -> e -ED- d ->> e' -> 
  abortOvlpStateEnt e \/ badOvlpStateEnt e \/ listeningStateEnt e \/ pausedStateEnt e.
Proof.
  intros R DEL. destruct e as [p l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  destruct (listenerState_shape_ranged _ LS) as [H | [[m H] | [H | [[m H] | [H | [[m [l0 H]] |
    [[m [e [b [r [H _]]]]] | [[m [e [b [r [H _]]]]] | H]]]]]]]].
  - right; right; left. constructor; constructor; exact H.
  - exfalso. eapply ent_del_mCurr_in_not; [ | exact DEL]. intro m0. dae_listener.
    eapply rangeBad_mCurr_in. exact H.
  - right; left. constructor; constructor; exact H.
  - exfalso. eapply ent_del_mStable_mNext_in_not; [ | | exact DEL].
    + dae_listener. eapply currOK_mStable_in. exact H.
    + intro m0. dae_listener. eapply currOK_mNext_in. exact H.
  - left. constructor; constructor; exact H.
  - exfalso. eapply ent_del_pos_in_not with (l0 := l); [ | exact DEL]. dae_listener.
    eapply gotMsg_pos_in. exact H.
  - exfalso. eapply ent_del_mCurr_in_not; [ | exact DEL]. intro m0. dae_listener.
    eapply gotRange_mCurr_in_shape. exact H.
  - exfalso. eapply ent_del_mStable_mNext_in_not; [ | | exact DEL].
    + dae_listener. eapply currComp_mStable_in_shape. exact H.
    + intro m0. dae_listener. eapply currComp_mNext_in_shape. exact H.
  - right; right; right. constructor; constructor; exact H.
Qed.
(**Proof: Since the entity is reachable, we know it has a listener
component (...reachableProt_triple...), so we do a case analysis as to what the location
of the listener component is. In most cases, we can show by simple urgency results that
a discrete action is possible via the listener synchronising with another component of
the entity. The remaining cases that aren't urgent are exactly the conclusion to this
result, and we're done.*)

(** The listener in badOvlp outputs on bad.*)
Local Lemma badOvlp_bad_out p : badOvlpState p -> discActEnabled p (chanBad *!).
Proof. activation_tac. Qed.

Lemma tfsListen_urgent : forall (e e' : Entity) (d : Delay),
  reachableProtEnt e -> tfsListenStateEnt e -> e -ED- d ->> e' 
  -> False.
Proof.
  intros e e' d R TL D.
  destruct (del_listening_pre _ _ _ R D) as [S | [S | [S | S]]];
    destruct e' as [p' l' h' k']; ent_state_destr TL p1 p2 p3 l h k; ent_state_comp S;
    lets DP : link_ent_soft_del D.
  - triple_del_sync_not DP (tfsListen_abort_in _ TL) (abortOvlp_abort_out _ S).
  - triple_del_sync_not DP (tfsListen_bad_in _ TL) (badOvlp_bad_out _ S).
  - triple_del_sync_not DP (tfsListen_unpause_out _ TL) (listening_unpause_in _ S).
  - triple_del_sync_not DP (tfsListen_unpause_out _ TL) (paused_unpause_in _ S).
Qed.

(*Gives the possible states of the overlap component if a delay is possible.*)
Theorem del_ovlp (e e' : Entity) (d : Delay) : 
  reachableProtEnt e -> e -ED- d ->> e' ->
  dormantStateEnt e \/ tfsCurrStateEnt e \/
  exists m, exists t, exists x, exists y, ovWaitStateEnt m t x y e .
Proof.
  intros R DEL. destruct e as [p l h k].
  lets PS : reachableProt_triple (reachable_ent_prot _ _ _ _ R).
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  destruct (delaying_overlap_states _ _ _ _ _ _ _ _ R DEL)
    as [X | [[m [e2 [e3 [e4 X]]]] | [X | X]]].
  - left. constructor; constructor; exact X.
  - (* ovWait, with times for its timers, as in a reachable entity *)
    right; right.
    destruct (transTimer_bound_ent _ R p1 p2 p3 l h k eq_refl) as [_ [_ [I2 _]]].
    assert (XW : exists m t x y, ovWaitStateExp m t x y p2) by (do 4 eexists; exact X).
    destruct (I2 XW) as [m1 [t1 [x1 [y1 [_ [_ [_ [X1 _]]]]]]]].
    exists m1 t1 x1 y1. constructor; constructor; exact X1.
  - right; left. constructor; constructor; exact X.
  - (* tfsListen synchronises with the listener *)
    exfalso. refine (tfsListen_urgent _ _ _ R _ DEL). constructor; constructor; exact X.
Qed.
(**Proof: Case analyse the overlap component of the software
process in e and eliminate most other possibilities by simple urgency results.
For the tfsListen case, apply (del_listening_pre). A corollary of this is that
the listener component is always capable of input on unpause or output on bad
or abort, and since tfsListen can do all three, a synch is always possible,
hence our urgency by progress. This should cover all states except those in our
conclusion, and we're done.*)

(** ovWait, whatever its timers, takes an output on bad.*)
Local Lemma ovWait_bad_in_shape (m : Mode) (e2 e3 e4 : Exp) p : p ~p~ ovWait m e2 e3 e4 ->
  discActEnabled p (chanBad *?).
Proof. activation_tac. Qed.

(**A reachable entity that can delay is in the listening state.*)
Theorem del_listening (e e' : Entity) (d : Delay) :
  reachableProtEnt e -> e -ED- d ->> e' -> listeningStateEnt e.
Proof.
  intros R DEL.
  destruct (del_listening_pre _ _ _ R DEL) as [Y | [Y | [Y | Y]]]; [ | | exact Y | ]; exfalso.
  - exact (abortOvlpStateEnt_urgent _ _ _ R Y DEL).
  - (* the overlap component takes badOvlp's output on bad *)
    destruct (del_ovlp _ _ _ R DEL) as [X | [X | [m [t [x [y X]]]]]];
      ent_state_destr Y p1 p2 p3 l h k; ent_state_comp X;
      destruct e' as [p' l' h' k']; lets DP : link_ent_soft_del DEL;
      lets BO : badOvlp_bad_out Y.
    + triple_del_sync_not DP (dormant_bad_in _ X) BO.
    + triple_del_sync_not DP (tfsCurr_bad_in _ X) BO.
    + triple_del_sync_not DP (ovWait_bad_in_shape _ _ _ _ _ X) BO.
  - (* a paused listener has the overlap component in a switch state, which del_ovlp excludes *)
    assert (SW : switchStateEnt e) by (apply (paused_switch_ent _ R); exact Y).
    destruct (del_ovlp _ _ _ R DEL) as [X | [X | [m [t [x [y X]]]]]];
      ent_state_destr SW p1 p2 p3 l h k; ent_state_comp X;
      destruct SW as [m0 SP | SP | SP]; ov_states_disj X SP.
Qed.
(**Proof: First we apply (del_listening_pre), to get that
we are either in abortOvlp, badOvlp, paused or listening. If the last case
is true, then we are done. From here, we apply (del_ovlp) to further get
dormant, tfsCurr or ovWait as possibilities for the current state. Now,
if we are paused, then by (paused_switch_ent) we are switchState- but this
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
  assert (ACT : forall b, p3 -PA- b -PA> p3' -> entChanAct b).
  { intros b B. destruct (currOK_next_act _ _ _ _ B G) as [[Eb _] | [v [Eb _]]];
      subst b; left; reflexivity. }
  destruct (triple_disc_ent_chan 2 R S eq_refl eq_refl ACT) as [EQ | S3];
    [subst p3'; left; constructor; constructor; exact G | ].
  destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S3) as [EQ | [c [T3 [_ [_ NX]]]]];
    [subst p3'; left; constructor; constructor; exact G | ].
  destruct (currOK_next_act _ _ _ _ T3 G) as [[Ec L] | [v [Ec N]]]; subst c.
  - right. left. constructor. constructor. exact L.
  - destruct (NX v eq_refl) as [NM _].
    right. right. exists v. split; [constructor; constructor; exact N | exact NM].
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
  assert (ACT : forall b, p3 -PA- b -PA> p3' -> entChanAct b).
  { intros b B. destruct (gotRange_next_act _ _ _ _ _ B G) as [v [Eb _]]. subst b.
    left. reflexivity. }
  destruct (triple_disc_ent_chan 2 R S eq_refl eq_refl ACT) as [EQ | S3];
    [subst p3'; left; constructor; constructor; exact G | ].
  destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S3) as [EQ | [c [T3 [_ [CR _]]]]];
    [subst p3'; left; constructor; constructor; exact G | ].
  destruct (gotRange_next_act _ _ _ _ _ T3 G) as [v [Ec C]]. subst c.
  destruct (CR v eq_refl) as [Ev _]. subst v.
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
  assert (ACT : forall b, p3 -PA- b -PA> p3' -> entChanAct b).
  { intros b B. destruct (rangeBad_next_act _ _ _ _ B G) as [v [Eb _]]. subst b.
    left. reflexivity. }
  destruct (triple_disc_ent_chan 2 R S eq_refl eq_refl ACT) as [EQ | S3];
    [subst p3'; left; constructor; constructor; exact G | ].
  destruct (ent_disc_proc_act _ _ _ _ _ _ _ _ _ S3) as [EQ | [c [T3 [_ [CR _]]]]];
    [subst p3'; left; constructor; constructor; exact G | ].
  destruct (rangeBad_next_act _ _ _ _ T3 G) as [v [Ec C]]. subst c.
  destruct (CR v eq_refl) as [Ev _]. subst v.
  right. simpl. constructor. constructor. exact C.
Qed.
(*+*)

  (*Add entity-level tracking result.*)
(*+*)

(** In a reachable entity, a step from ovReady into ovWait is the overlap component's broadcast
of its mode and the entity's position, which the interface takes in; the mode state and the
mode stay the same.*)
Lemma ovReady_ovWait_bcast_ent m m' t t' x' y' l0 a p p' l l' h h' k k' :
  reachableProtEnt ([|p, l, h, k|]) ->
  ovReadyStateEnt m t l0 ([|p, l, h, k|]) ->
  ovWaitStateEnt m' t' x' y' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p -PA- chanOutProc ;! [baseMode m, basePosition l0] -PA> p' /\
  h -i- chanOutProc {? [baseMode m, basePosition l0] -i> h' /\
  k = k' /\ m = m' /\ l = l0.
Proof.
  intros R OR OW S. pose proof OR as OR0.
  pose proof (reachable_ent_prot _ _ _ _ R) as RP.
  lets PS : reachableProt_triple RP. lets CU : reachableProt_correctChannelUsage RP.
  inversion PS as [p1 p2 p3 BS OS LS]; subst p.
  ent_state_comp OR.
  inversion OW as [q lq hq kq OWq]; subst.
  inversion OWq as [p1' p2' p3' OW2]; subst.
  (* the overlap component only broadcasts *)
  assert (PD : forall b, p2 -PA- b -PA> p2' ->
    b = chanOutProc ;! [baseMode m, basePosition l0] /\
    p2' ~p~ ovWait m (t (-) ePeriod m) (t (-) ePeriod m) (ePeriod m)).
  { intros b B. destruct (bisim_step_disc _ _ _ _ OR B) as [q [SQ BQ]].
    destruct (ovReady_step_ovWait _ _ _ _ _ SQ) as [EB BW]. split; [exact EB | ].
    eapply bisim_trans; [exact BQ | exact BW]. }
  assert (NE : p2 <> p2').
  { intro EQ. subst p2'. eapply ovReady_ovWait_bisim_not.
    eapply bisim_trans; [apply bisim_symm; exact OW2 | exact OR]. }
  assert (ACT : forall b, p2 -PA- b -PA> p2' -> entChanAct b).
  { intros b B. destruct (PD b B) as [EB _]. subst b. right. reflexivity. }
  change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in S, CU.
  change (p1' $||$ p2' $||$ p3') with (parAll p1' [p2', p3']) in S.
  destruct (ent_disc_comp_chan _ _ _ _ _ _ _ _ _ _ _ _ _ 1 p2 p2' CU S eq_refl eq_refl eq_refl ACT)
    as [EQ | St]; [contradiction | ].
  positions_inv.
  match goal with [S2 : [|p2, l, h, k|] -EA- a ->> [|p2', l', h', k'|] |- _] =>
    inversion S2; subst; try (exfalso; apply NE; reflexivity);
    try (match goal with [B : p2 -PA- _ -PA> p2' |- _] =>
      destruct (PD _ B) as [EB _]; discriminate EB end) end.
  match goal with [B : p2 -PA- chanOutProc ;! ?v -PA> p2' |- _] =>
    destruct (PD _ B) as [EB BW]; injection EB as EB; subst v end.
  assert (BW' : ovWait m (t (-) ePeriod m) (t (-) ePeriod m) (ePeriod m) ~p~ ovWait m' t' x' y')
    by (eapply bisim_trans; [apply bisim_symm; exact BW | exact OW2]).
  split; [ | split; [assumption | split; [reflexivity | split]]].
  - apply stepDpParR. apply stepDpParL. assumption.
  - exact (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _ (evalExpFunTime_period m) BW')).
  - exact (ovReady_pos _ _ _ _ R OR0).
Qed.

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
Local Lemma tfsCurr_next p p' b :
  p -PA- b -PA> p' -> tfsCurrState p -> tfsCurrState p' \/ tfsBcState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsCurr_next_ent e e' a :
  e -EA- a ->> e' -> tfsCurrStateEnt e ->
  tfsCurrStateEnt e' \/ tfsBcStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsCurrState tfsBcState _ _ _ tfsCurr_next S T).
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
Local Lemma tfsBc_next p p' b :
  p -PA- b -PA> p' -> tfsBcState p -> tfsBcState p' \/ tfsListenState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsBc_next_ent e e' a :
  e -EA- a ->> e' -> tfsBcStateEnt e ->
  tfsBcStateEnt e' \/ tfsListenStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsBcState tfsListenState _ _ _ tfsBc_next S T).
Qed.

(* begin helpers for tfsListen_next_ent *)
(** Process-level forward tracking from the tfsListen state
(uses the #fwd-track-lift-ent support from tfsCurr_next_ent).*)
Local Lemma tfsListen_next p p' b :
  p -PA- b -PA> p' -> tfsListenState p -> tfsListenState p' \/ dormantState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsListen_next_ent e e' a :
  e -EA- a ->> e' -> tfsListenStateEnt e ->
  tfsListenStateEnt e' \/ dormantStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsListenState dormantState _ _ _ tfsListen_next S T).
Qed.

(*- LOCAL TIDY*)