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
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults.
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.NARMisc.
Require Import ComhCoq.protocol.NAROvlpTime.
Require Import ComhCoq.protocol.ProtocolBridge.

Section NARNonFS_currSince.
Context {Model : ComhModel}.

Lemma ovWait_nextSinceState_net m t x y i n : 
  ovWaitStateNet m t x y i n -> nextSinceStateNet i n.
Proof.
  intro U. destruct U as [e U1 U2]. destruct U1 as [q l h k U3].
  destruct U3 as [p1 p p3 U4]. econstructor;[ | exact U2].
  constructor. constructor. econstructor. exact U4. Qed.
(*Proof: Is there some auto tactic for this? #lift-compound-net-tac*)

(** In an initial network every overlap component is dormant.*)
Local Lemma initial_overlap_dormant (Z : ProcTerm -> Prop) n i :
  initialProtNet n -> liftEntNet (liftProcEnt (liftOverlap Z)) i n -> Z dormant.
Proof.
  intros I Q. net_state_destr Q p1 p2 p3 l h k E.
  lets IE : initialNet_ent I E. inversion IE; subst. exact Q.
Qed.

(** An expression with no free variable.*)
Local Definition closedExp (e : Exp) : Prop := forall s, subExp s e = e.

Local Lemma closedExp_subtract_period e (m : Mode) : closedExp e -> closedExp (e (-) ePeriod m).
Proof. intros C s. simpl. rewrite (C s). reflexivity. Qed.

(** ovWait delays into ovWait for the same mode and first parameter, whose pause timer is well
formed just when it was, and whose position timer is well formed if it was.*)
Local Lemma ovWait_del_wellformed (m : Mode) e2 e3 e4 d q :
  ovWait m e2 e3 e4 -PD- d -PD> q ->
  exists e3' e4', q ~p~ ovWait m e2 e3' e4' /\
    ((exists t3, evalExpFunTime e3 = Some t3) <-> (exists t3, evalExpFunTime e3' = Some t3)) /\
    ((exists t4, evalExpFunTime e4 = Some t4) -> exists t4, evalExpFunTime e4' = Some t4).
Proof.
  unfold ovWait. intro D. invert_del_prefixes.
  all: do 2 eexists; split; [del_timers_bisim | ].
  all: split; [split | ]; intros [? ?]; eexists; first [eassumption | apply evalExpFunTime_time].
Qed.

(** A reachable overlap component in ovWait is bisimilar to one whose first parameter has no free
variable, whose pause timer is well formed just when that parameter is, and whose position timer
is well formed; in ovReady, to one whose timer has no free variable.*)
Local Definition ovClosedShape (p : ProcTerm) : Prop :=
  ((forall (m : Mode) e2 e3 e4, p ~p~ ovWait m e2 e3 e4 -> False) /\
   (forall (m : Mode) e2 (l : Position), p ~p~ ovReady m e2 l -> False)) \/
  (exists (m : Mode) e2 e3 e4, p ~p~ ovWait m e2 e3 e4 /\ closedExp e2 /\
     ((exists t2, evalExpFunTime e2 = Some t2) <-> (exists t3, evalExpFunTime e3 = Some t3)) /\
     exists t4, evalExpFunTime e4 = Some t4) \/
  (exists (m : Mode) e2 (l : Position), p ~p~ ovReady m e2 l /\ closedExp e2).

Local Lemma ocs_wait p (m : Mode) e2 e3 e4 : p ~p~ ovWait m e2 e3 e4 -> closedExp e2 ->
  ((exists t2, evalExpFunTime e2 = Some t2) <-> (exists t3, evalExpFunTime e3 = Some t3)) ->
  (exists t4, evalExpFunTime e4 = Some t4) -> ovClosedShape p.
Proof. intros W C L E. right. left. exists m e2 e3 e4. exact (conj W (conj C (conj L E))). Qed.

Local Lemma ocs_ready p (m : Mode) e2 (l : Position) :
  p ~p~ ovReady m e2 l -> closedExp e2 -> ovClosedShape p.
Proof. intros R C. right. right. exists m e2 l. exact (conj R C). Qed.

(** Refutes B : X ~p~ Y for overlap states X and Y, named or unfolded, that differ on a
channel.*)
Local Ltac ov_contra B :=
  prot_outProc_in_not_body; try unfold liftNameProc in B; try unfold liftVarList in B;
  refute_by_chan B.

(** Proves ovClosedShape q from B : q ~p~ X, for X neither ovWait nor ovReady.*)
Local Ltac ocs_other B :=
  left; split;
  [ intros ?m ?e2 ?e3 ?e4 ?W;
    let BT := fresh "BT" in pose proof (bisim_trans _ _ _ (bisim_symm _ _ B) W) as BT;
    try unfold_app_hyp_l BT; ov_contra BT
  | intros ?m ?e2 ?l ?W;
    let BT := fresh "BT" in pose proof (bisim_trans _ _ _ (bisim_symm _ _ B) W) as BT;
    try unfold_app_hyp_l BT; ov_contra BT ].

Local Lemma overlapState_closed p : overlapState p -> ovClosedShape p.
Proof.
  intro O. cut (overlapShape p /\ ovClosedShape p); [tauto | ].
  revert O. unfold overlapState.
  apply (reachableFrom_invariant (fun p => overlapShape p /\ ovClosedShape p) dormant p).
  - split; [apply shDormant, bisim_refl | ]. pose proof (bisim_refl dormant) as B. ocs_other B.
  - intros q q' a [SH CS] T. split; [eapply overlapShape_disc; eassumption | ].
    destruct CS as [[NW NR] | [[m [e2 [e3 [e4 [W [C [L E]]]]]]] | [m [e2 [l [R C]]]]]].
    + destruct SH as [H | m H | m e2 e3 e4 H | m e2 l H | m H | H | H | H | H | m H | H | H | H];
        try (exfalso; eapply NW; exact H); try (exfalso; eapply NR; exact H);
        shape_step_pre B;
        first [ ocs_other B
              | eapply ocs_wait; [shape_body B | intro s; reflexivity | reflexivity
                  | exists zeroTime; apply evalExpFunTime_time ] ].
    + destruct (bisim_step_disc _ _ _ _ W T) as [D [TD BD]]. clear W T.
      unfold ovWait in TD. invert_disc_prefixes; try (unfold liftVarList in *);
        explicit_typed_input; try (unfold liftNameProc in BD); clean_proc_hyp BD;
        first [ ocs_other BD | (eapply ocs_ready; [shape_body BD | rewrite C; exact C]) ].
    + destruct (bisim_step_disc _ _ _ _ R T) as [D [TD BD]]. clear R T.
      unfold ovReady in TD. invert_disc_prefixes. output_values. clean_proc_hyp BD.
      eapply ocs_wait; [shape_body BD | apply closedExp_subtract_period; exact C | reflexivity
        | exists (period m); apply evalExpFunTime_period ].
  - intros q q' d [SH CS] T. split; [eapply overlapShape_del; eassumption | ].
    destruct CS as [[NW NR] | [[m [e2 [e3 [e4 [W [C [L [t4 E]]]]]]]] | [m [e2 [l [R C]]]]]].
    + destruct SH as [H | m H | m e2 e3 e4 H | m e2 l H | m H | H | H | H | H | m H | H | H | H];
        try (exfalso; eapply NW; exact H); try (exfalso; eapply NR; exact H);
        (match type of H with _ ~p~ ?X =>
           let B := fresh "B" in
           assert (B : q' ~p~ X) by (eapply bisim_del_pres; [del_self_body | exact H | exact T]);
           ocs_other B end).
    + destruct (bisim_step_del _ _ _ _ W T) as [D [TD BD]].
      destruct (ovWait_del_wellformed _ _ _ _ _ _ TD) as [e3' [e4' [BW [L3 L4]]]].
      eapply ocs_wait; [exact (bisim_trans _ _ _ BD BW) | exact C | exact (iff_trans L L3)
        | exact (L4 (ex_intro _ t4 E))].
    + eapply ocs_ready; [eapply bisim_del_pres; [del_self_body | exact R | exact T] | exact C].
Qed.

(** Of bisimilar ovReady for one mode, the second with a time as its timer, the first has a timer
that evaluates to a time equal to it up to the period.*)
Local Lemma ovReady_bisim_timer_val (m : Mode) (u : Exp) (t : Time) (l1 l2 : Position) :
  ovReady m u l1 ~p~ ovReady m t l2 ->
  exists tu, evalExpFunTime u = Some tu /\
    time tu -nn- time (period m) = time t -nn- time (period m).
Proof.
  intro B.
  assert (S2 : exists q, ovReady m t l2 -PA- chanOutProc ;! [baseMode m, basePosition l2] -PA> q)
    by (eexists; unfold ovReady; apply stepDpOut; repeat constructor).
  destruct S2 as [q2 S2].
  destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ B) S2) as [q1 [S1 BQ]].
  destruct (ovReady_step_ovWait _ _ _ _ _ S1) as [_ W1].
  destruct (ovReady_step_ovWait _ _ _ _ _ S2) as [_ W2].
  pose proof (bisim_trans _ _ _ (bisim_symm _ _ W1)
    (bisim_trans _ _ _ (bisim_symm _ _ BQ) W2)) as BW.
  lets EX : ovWait_bisim_pause_timer BW
    (evalExpFunTime_subtract_period m _ t (evalExpFunTime_time t)).
  destruct (evalExpFunTime_subtract_inv _ _ _ EX) as [tu EU].
  exists tu. split; [exact EU | ].
  rewrite (evalExpFunTime_subtract_period m u tu EU) in EX. injection EX as EX. exact EX.
Qed.

(** While entity i is pending, its wait has its position timer run out and a positive pause
timer.*)
Local Lemma pending_ovWait_timers i n p : pending i n p ->
  forall m t x y, ovWaitStateNet m t x y i n -> y = zeroTime /\ 0 < x.
Proof.
  intro PE. induction PE as [a n n' p w m0 t0 x0 y0 IS OW | a n n' p w m0 t0 x0 y0 PE IH OW OW'
    | a n n' p w m0 l0 t0 x0 y0 PE IH OW OR | a n n' p w m0 l0 t0 PE IH OR OR'];
    intros m t x y Q.
  - (* init has just set the timers *)
    destruct (init_ovWait_timers_net _ _ _ _ _ _ _ _ _ IS Q w) as [EM [EY [[m1 [pr XV]] _]]].
    subst m0. split; [exact EY | ]. rewrite XV.
    pose proof (cond_nonneg (time (waitTime m1 m pr))). pose proof (period_positive m). lra.
  - (* the timers are those of the wait before the step *)
    pose proof (overlap_states_bisim_net _ _ _ _ Q OW') as B.
    lets EX : ovWait_bisim_pause_timer B (evalExpFunTime_time x0).
    lets EY : ovWait_bisim_pos_timer B (evalExpFunTime_time y0).
    rewrite evalExpFunTime_time in EX, EY. injection EX as EX. injection EY as EY. subst x y.
    exact (IH _ _ _ _ OW).
  - exfalso. eapply ovReady_ovWait_bisim_not. exact (overlap_states_bisim_net _ _ _ _ Q OR).
  - exfalso. eapply ovReady_ovWait_bisim_not. exact (overlap_states_bisim_net _ _ _ _ Q OR').
Qed.

(** What the history relations say of the overlap component of entity i: in ovWait and ovReady
it is pending or nextSince its mode, in switchBc nextSince its mode, and in switchCurr nextSince
some mode.*)
Local Definition overlapHistory (i : nat) (n : Network) (p : reachableProtNet n) : Prop :=
  (forall m t x y, ovWaitStateNet m t x y i n -> pending i n p \/ exists t', nextSince m t' i n p) /\
  (forall m t l, ovReadyStateNet m t l i n -> pending i n p \/ exists t', nextSince m t' i n p) /\
  (forall m, switchBcStateNet m i n -> exists t', nextSince m t' i n p) /\
  (switchCurrStateNet i n -> exists m t', nextSince m t' i n p).

Local Lemma overlapHistory_reachable n (p : reachableProtNet n) i : overlapHistory i n p.
Proof.
  induction p as [n I | n n' a p IH w | n n' d p IH w].
  - (* the overlap component is dormant at first *)
    split; [intros m t x y Q | split; [intros m t l Q | split; [intros m Q | intro Q]]];
      exfalso; pose proof (initial_overlap_dormant _ _ _ I Q) as B; red in B; ov_contra B.
  - destruct IH as [IW [IR [IB IC]]].
    split; [ | split; [ | split]].
    + (* ovWait: waiting already, the broadcast of ovReady, or init *)
      intros m t x y OW.
      pose proof (ovWait_nextSinceState_net _ _ _ _ _ _ OW) as NSS.
      destruct (ovWait_prev_net _ _ _ _ _ _ _ _ p OW w) as [OW0 | [[t0 [l0 [R0 _]]] | IS]].
      * destruct (IW _ _ _ _ OW0) as [PE | [t' NS]].
        -- left. eapply pendingWait; eassumption.
        -- right. exists t'. apply nextSinceDisc; assumption.
      * right. destruct (IR _ _ _ R0) as [PE | [t' NS]].
        -- exists zeroTime. eapply nextSinceBase; eassumption.
        -- exists t'. apply nextSinceDisc; assumption.
      * left. eapply pendingBase; eassumption.
    + (* ovReady: ready already, or the position read of ovWait *)
      intros m t l OR.
      pose proof (ovReady_nextSince_state _ _ _ _ _ OR) as NSS.
      destruct (overlap_disc_net_cases _ _ _ _ _ p w OR) as [p2 [p2' [OS [[EQ | [b B2]] [V V']]]]].
      * subst p2'. destruct (IR _ _ _ (proj2 (V _) (proj1 (V' _) OR))) as [PE | [t' NS]].
        -- left. eapply pendingReady; [exact PE | exact (proj2 (V _) (proj1 (V' _) OR)) | exact OR].
        -- right. exists t'. apply nextSinceDisc; assumption.
      * pose proof (proj1 (V' _) OR) as Q2.
        destruct (ovReadyExp_prev _ _ _ _ _ _ B2 OS Q2) as [e2 [e3 [e4 W]]].
        destruct (overlapState_closed _ OS)
          as [[NW _] | [[m1 [e2c [e3c [e4c [WC [C [L _]]]]]]] | [m1 [e2c [l1 [RC _]]]]]].
        -- exfalso. exact (NW _ _ _ _ W).
        -- (* the read of the closed wait, whose position timer had run out *)
           destruct (bisim_step_disc _ _ _ _ WC B2) as [D [TD BD]].
           pose proof (bisim_trans _ _ _ (bisim_symm _ _ BD) Q2) as BT.
           unfold ovWait in TD. invert_disc_prefixes; explicit_typed_input; clean_proc_hyp BT;
             try solve [exfalso; unfold_app_hyp_l BT; prot_outProc_in_not_body; refute_by_chan BT].
           rewrite C in BT.
           pose proof (bisim_trans _ _ _ (bisim_symm _ _ (ovReadyN_bisim _ _ _)) BT) as BR.
           pose proof (ovReady_bisim_mode _ _ _ _ _ _ BR) as EM. subst m1.
           destruct (ovReady_bisim_timer_val _ _ _ _ _ BR) as [tu [EU FV]].
           destruct (proj1 L (ex_intro _ tu EU)) as [tx EX].
           match goal with [E4 : evalExpFunTime e4c = Some zeroTime |- _] =>
             pose proof (ovWaitStateExp_time _ _ _ _ _ _ _ _ EU EX E4 WC) as W0 end.
           pose proof (proj2 (V _) (ovWaitState_period _ _ _ _ _ _ FV W0)) as OW0.
           destruct (IW _ _ _ _ OW0) as [PE | [t' NS]].
           ++ left. eapply pendingWaitReady; eassumption.
           ++ right. exists t'. apply nextSinceDisc; assumption.
        -- exfalso. eapply ovReady_ovWait_bisim_not.
           exact (bisim_trans _ _ _ (bisim_symm _ _ W) RC).
    + (* switchBc: there already, or the pause of ovWait, whose pause timer had run out *)
      intros m SB.
      assert (NSS : nextSinceStateNet i n').
      { pose proof SB as SB0. net_state_destr SB0 q1 q2 q3 l h k E. net_state_intro E.
        exact (nexsSbcSt _ m SB0). }
      destruct (overlap_disc_net_cases _ _ _ _ _ p w SB) as [p2 [p2' [OS [[EQ | [b B2]] [V V']]]]].
      * subst p2'. destruct (IB _ (proj2 (V _) (proj1 (V' _) SB))) as [t' NS].
        exists t'. apply nextSinceDisc; assumption.
      * destruct (switchBc_prev _ _ _ _ B2 OS (proj1 (V' _) SB)) as [e2 [e4 WE]].
        destruct (overlapState_closed _ OS)
          as [[NW _] | [[m1 [e2c [e3c [e4c [WC [_ [L [t4 E4]]]]]]]] | [m1 [e2c [l1 [RC _]]]]]].
        -- exfalso. exact (NW _ _ _ _ WE).
        -- pose proof (bisim_trans _ _ _ (bisim_symm _ _ WC) WE) as BW.
           lets E3 : ovWait_bisim_pause_timer BW (evalExpFunTime_time zeroTime).
           destruct (proj2 L (ex_intro _ _ E3)) as [tu EU].
           pose proof (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _ E4 BW)) as EM. subst m1.
           pose proof (proj2 (V _) (ovWaitStateExp_time _ _ _ _ _ _ _ _ EU E3 E4 WC)) as OW0.
           destruct (IW _ _ _ _ OW0) as [PE | [t' NS]].
           ++ exfalso. destruct (pending_ovWait_timers _ _ _ PE _ _ _ _ OW0) as [_ XP].
              simpl in XP. lra.
           ++ exists t'. apply nextSinceDisc; assumption.
        -- exfalso. eapply ovReady_ovWait_bisim_not.
           exact (bisim_trans _ _ _ (bisim_symm _ _ WE) RC).
    + (* switchCurr: there already, or the wake of switchBc *)
      intro SC.
      assert (NSS : forall m0 : Mode, nextSinceStateNet i n').
      { intro m0. pose proof SC as SC0. net_state_destr SC0 q1 q2 q3 l h k E. net_state_intro E.
        exact (nexsScSt _ m0 SC0). }
      destruct (overlap_disc_net_cases _ _ _ _ _ p w SC) as [p2 [p2' [OS [[EQ | [b B2]] [V V']]]]].
      * subst p2'. destruct (IC (proj2 (V _) (proj1 (V' _) SC))) as [m [t' NS]].
        exists m t'. apply nextSinceDisc; [exact NS | exact (NSS m)].
      * destruct (switchCurr_prev _ _ _ B2 OS (proj1 (V' _) SC)) as [m0 SB0].
        destruct (IB _ (proj2 (V _) SB0)) as [t' NS].
        exists m0 t'. apply nextSinceDisc; [exact NS | exact (NSS m0)].
  - destruct IH as [IW [IR [IB IC]]].
    split; [ | split; [ | split]].
    + (* ovWait: a pending wait cannot let time pass *)
      intros m t x y OW.
      destruct (reachableProtNet_del_prev _ _ _ _ _ p w OW) as [_ [OS _]].
      destruct (ovWait_del_bkwd_net _ _ _ _ _ _ _ _ OS w OW) as [x0 OW0].
      destruct (IW _ _ _ _ OW0) as [PE | [t' NS]].
      * exfalso. destruct (pending_ovWait_timers _ _ _ PE _ _ _ _ OW0) as [EY _].
        apply (f_equal (fun z => nonneg (time z))) in EY. simpl in EY.
        pose proof (cond_nonneg (time y)). pose proof (cond_pos (delay d)). lra.
      * right. exists (t' +dt+ d). apply nextSinceDel. exact NS.
    + (* ovReady cannot let time pass *)
      intros m t l OR. exfalso.
      destruct (reachableProtNet_del_prev _ _ _ _ _ p w OR) as [_ [OS _]].
      destruct (ovReady_del_pres_bkwd_net _ _ _ _ _ _ _ OS w OR) as [e OE E].
      destruct (link_net_ent_del_fwd _ _ _ _ _ w E) as [e' [_ DE]].
      exact (ovReady_urgent m t l e e' d OE DE).
    + intros m SB.
      destruct (reachableProtNet_del_prev _ _ _ _ _ p w SB) as [_ [OS _]].
      assert (SB0 : switchBcStateNet m i n)
        by (apply (overlap_del_bkwd_net (switchBc m) _ _ _ _ OS w SB); intros m0 e2 e3 e4 B;
            ovWait_bisim_contra B).
      destruct (IB _ SB0) as [t' NS]. exists (t' +dt+ d). apply nextSinceDel. exact NS.
    + intro SC.
      destruct (reachableProtNet_del_prev _ _ _ _ _ p w SC) as [_ [OS _]].
      assert (SC0 : switchCurrStateNet i n)
        by (apply (overlap_del_bkwd_net switchCurr _ _ _ _ OS w SC); intros m0 e2 e3 e4 B;
            ovWait_bisim_contra B).
      destruct (IC SC0) as [m [t' NS]]. exists m (t' +dt+ d). apply nextSinceDel. exact NS.
Qed.

(** An entity in switchCurr is nextSince some mode.*)
Lemma switchCurr_nextSince_ex n (p : reachableProtNet n) i :
  switchCurrStateNet i n -> exists m t, nextSince m t i n p.
Proof. exact (proj2 (proj2 (proj2 (overlapHistory_reachable n p i)))). Qed.

(*If we are in the switchCurr state, changing to mode m, then the nextSince relation holds
for m.*)
Theorem switchCurr_nextSince (n : Network) (m : Mode) (i : nat)
  (p : reachableProtNet n) : nextModeNet m i n -> switchCurrStateNet i n ->
  exists t, nextSince m t i n p.
(**Proof: By induction on reachable and (...switchCurr_prev...) to give us switchBc m
as the predecessor state. Then by (swtichBc_nextSince) and application of the nextSince
discrete constructor our results follows.*)
Proof.
  intros NM SC. destruct (switchCurr_nextSince_ex n p i SC) as [m' [t NS]].
  pose proof (nextSince_next _ _ _ _ _ NS) as NM'.
  rewrite nextMode_ent_ex in NM, NM'. destruct NM as [e [E1 N1]], NM' as [e' [E2 N2]].
  assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
  rewrite N1 in N2. injection N2 as N2. subst m'. exists t. exact NS.
Qed.

(* Let's say in a reachable network, an entity is in non-fail-safe mode m.
Then that entity has been currSince m t.*)
Theorem nonFS_currSince (m : Mode) (i : nat) (n : Network) 
  (p : reachableProtNet n) : currModeNet m i n -> ~failSafe m ->
  exists t, currSince m t i n p.
  intros.
  (**Proof: Induction on the proof of reachability of n.*)
  induction p.
  (*In the base case, we have that n is initial. Hence all its constituent entities
  are in fail safe modes. So the assumption that entity i is in mode m which is not
  fail safe is contradictory, case closed.*)
  apply currMode_ent_ex in H. decompose [ex] H. clear H. rename x into e.
  invertClear H1. rewrite <- H2 in H0. apply False_ind. apply H0.
  eapply initial_failSafe. apply i0. apply H.
  (*Which leaves us the inductive cases. We start with the discrete inductive case.
  Here, we do a case analysis on whether the previous state was currMode m.*)
  addHyp (currModeNet_dec m i n). invertClear H1.
  (*If it was, then by the inductive hypothesis, we get currSince m t for
  the previous state*)
  apply IHp in H2. invertClear H2. rename x into t.
  (*Which immediately follows on to this state by the inductive definition of currSince.*)
  exists t. eapply currSinceDisc. apply H1. assumption.
  (*Otherwise, the previous state was not currMode m. And so it must have been currMode m'
  for some m' <> m (Basics::currMode_pres_bkwd).*)
  addHyp (currMode_pres_bkwd n n' a m i s H). invertClear H1. rename x into m'.
  assert (m' <> m). unfold not. intros. rewrite H1 in H3. apply H2. assumption.
  (*And so we can show that since the current mode has changed between states,
  the entity i must have performed a tau transition.*)
  addHyp H. rewrite (currMode_ent_ex m i n') in H4.
  addHyp H3. rewrite (currMode_ent_ex m' i n) in H5.
  invertClear H4. invertClear H5. invertClear H4. invertClear H6.
  rename x0 into e. rename x into e'.
  addHyp (curr_switch_ent_tau n n' a e e' i m' m s H5 H4 H7 H8 H1).
  (*We can also show that the software component contributed an output on mCurr and the
  mode-state contributed an input (EA::curr_switch_proc).*)
  rename p into X. destruct e as [p l h k]. destruct e' as [p' l' h' k'].
  addHyp (currMode_ent_mState p l h k m' H7). addHyp (currMode_ent_mState p' l' h' k' m H8).
  assert (currModeMState k <> currModeMState k'). rewrite H9. rewrite H10. assumption.
  addHyp (curr_switch_proc p p' l l' h h' k k' H6 H11). invertClear H12.
  (*Now, we since n is reachable, so is p, and so p is a triple of processes*)
  addHyp (reachable_net_prot n i p l h k X H5). apply reachableProt_triple in H12.
  invertClear H12. rewrite <- H18 in H13. 
  (*And so one of the sub components P1, P2 or P3 must have performed this output.*)
  link_partripdiscex_tac Y p1' p2' p3'. rewrite Y in H13.
  link_partripout_tac U;[
  (*We eliminate the possibility P1 by (bc_mCurr_out_not)*)
  false; eapply bc_mCurr_out_not; [apply U | assumption] | |
  (*and we eliminate P3 with (listen_mCurr_not).*)
  false; eapply listen_mCurr_out_not; [apply U | assumption]].  
  (*Then by (...ovlp_mCurr_out...) we show that P2 was in the state switchCurrState,
  while the next state had P2' in switchListenState*)
  lets OO : ovlp_mCurr_out U H16.
  (*We can eliminate the tfs case because failSafe m contradicts our hypothesis.*)
  elim_intro OO SW TF. Focus 2.
  assert (tfsBcStateEnt ([|p', l', h', k'|])). constructor. rewrite Y.
  constructor. apply TF. apply tfsBc_failSafe in H12;
  [ | exact (reachable_net_ent _ _ _ (reachNetDisc n n' a X s) H4)].
  simpl in H12. rewrite H10 in H12. false.
  (*This allows us to conclude that the previous state was nextSince m t i n for some t
  (switchCurr_nextSince)*)
  assert (switchCurrStateEnt ([|p, l, h, k|])).
  constructor. rewrite <- H18. constructor. apply SW.
  assert (switchCurrStateNet i n). econstructor. apply H12. assumption.
  assert (NM : nextModeNet m i n).
  { rewrite nextMode_ent_ex. exists ([|p, l, h, k|]). split; [exact H5 | ].
    inversion H14 as [ | | | | | m0 m1 EK EK' | | | | | ]. simpl.
    match goal with [E : sing m1 = k' |- _] => rewrite <- E in H10 end.
    simpl in H10. rewrite H10. reflexivity. }
  addHyp (switchCurr_nextSince n m i X NM H19). invertClear H20.
  rename x into t.
  (*Now finally, by the base case of currSince, we can show that
  currSince m t i n holds.*)
  exists t. constructor. assumption. assumption. econstructor.
  constructor. constructor. apply SW. rewrite Y in H4. apply H4.
  (*For the delay inductive case, we first notice that delay preserves the current mode*)
  addHyp (currMode_del_pres_bkwd n n' d m i s H).
  (*Then we apply the I.H. to get that the previous mode was currSince.*)
  apply IHp in H1. invertClear H1. rename x into t.
  (*And now as our existential we take t + d*. And by the delay constructor of
  currSince, we're done.*)
  exists (t +dt+ d). constructor. assumption. Qed.

End NARNonFS_currSince.
