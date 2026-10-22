(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lra.

Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
(* Without its coercions and notations, which are ambiguous with those imported above. *)
Require Import -(coercions, notations) ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.protocol.ProtAuxDefs.
(*
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.EntityLanguage.*)
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.lang.ProcEquiv.
(*Require Import ComhCoq.EntAux.*)
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.EntAuxResults.
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.NetAuxDefs.
Require Import ComhCoq.protocol.NARMisc.
Require Import ComhCoq.protocol.ProtocolBridge.

Section NAROvlpTime.
Context {Model : ComhModel}.

(*If an entity is pending then it cannot delay.*)
Theorem pending_urgent (n n' : Network) (d : Delay) (i : nat) (p : reachableProtNet n) :
  pending i n p -> ~ n -ND- d -ND> n'. Admitted. (*1*)
(**Proof: *SPAWN SEPARATE URGENCY RESULTS FOR THIS DONE*
Induction on pending. We have 2 cases. Case 1 is that we are
ovWaitStateNet m t x 0 i n- the y parameter can be shown to be 0 (separate proof?).
In this case, the input on pos is enabled and so the process can't delay by
progress [salvaged?]. Case 2 is the ovReadyStateNet m t l i n', which is ready to
output on io. Again by progress this means a delay is not possible.*)

(* If an entity is pending, and the same entity is in the state
ovWaitState m u x y, then we can show that u is equal to tw(m0, m) + period m, for some m0.*)
Theorem pending_time1 (n : Network) (m : Mode) (i : nat)
  (u x y : Time) (p : reachableProtNet n) :
  pending i n p -> ovWaitStateNet m u x y i n -> exists m0 q,
  u = addTime (waitTime m0 m q) (period m). Admitted. (*1*)
(**Proof: COMMON TACTICS FOR THE ADDTIME SHIT? THERE ARE MORE THEOREMS OF A SIMILAR NATURE.
By induction on pending. In the base case, we have that the previous state was
init m and so by backtracking (...) we can show that y = 0 and u = tw(m0, m) + period m.
In the first inductive case, we can show that u does not change from one state to the next.
The other two inductive cases fail because they involve ovReadyState, which is not
ovWaitState.*)

(* If an entity is pending, and the same entity is in the state ovReadyState m u l,
then we can show that u is equal to tw(m0, m) + period m, for some m0.*)
Theorem pending_time2 (n : Network) (m : Mode) (i : nat)
  (u : Time) (l : Position) (p : reachableProtNet n) :
  pending i n p -> ovReadyStateNet m u l i n ->
  exists m0 q, u = addTime (waitTime m0 m q) (period m).
  Admitted. (*1*)
(**Proof: Induction on pending. BaseType case fails because it only applies to ovWait.
Discrete inductive case can be shown by (backtracking + automation) to follow from
ovWaitState m u t' i n. But then by (pending_time1), we have that u = tw(m0, m) + period m.
And since the u is the same across the transition, it holds now. The delay inductive case
fails because delay can be shown to be impossible when a state is pending (pending_urgent).*)

(*If an entity is nextSince m t, and the same entity is in the state ovReadyState m u l,
then t + u is constant, equal to the sum of the wait time to m from some mode, tw(m0, m)
and the period of broadcast for m, period m. This is the combination of two results*)
Theorem nextSince_ovWait_ovReady_time (n : Network) (m : Mode) (i : nat)
  (t u x y : Time) (l : Position) (p : reachableProtNet n) :
  (nextSince m t i n p -> ovWaitStateNet m u x y i n ->
  exists m0 q, addTime t x = waitTime m0 m q
  /\ addTime u y = addTime x (period m)) /\ (*Half theorem*)
  (nextSince m t i n p -> ovReadyStateNet m u l i n ->
  exists m0 q,
  addTime t u = addTime (waitTime m0 m q) (period m)). Admitted. (*1*)
(**Proof: Mutual induction on nextSince. We don't have to actually use mutual induction,
just effectively we will be by proving these two results together as a conjunction and
the splitting by case analysis later.
!Four applications of ovWait_prev?! could be tidied up! For ovWait: In the base case,
we have that the entity in the previous state was pending, and the previous state was
ovReadySate m u0 l for some u0, l. Well then, by (pending_time2), we have that
u0 = tw(m0, m) + period m, for some m. But we also have by (...ovWait_prev...)
that x = u = u0 - period m, after eliminating the initState possibility because
it causes a contradiction. So substituting for u0 and tidying up we have x = tw(m0, m).
And since this is the base case, t = 0. So t + x = tw(m0, m) as required. Also from
(...ovWait_prev...) we have that on entering the state u = x and y = period m.
So u = x - y + period m holds. In the delay inductive case, t increases and u decreases
proportionately. By the I.H. t + u = tw(m0, m), and so for a delay of d, the new sum
becomes (t + d) + (u - d) = t + u = tw(m0, m), and our constant sum is preserved.
Also, x and y decrease by this d. So we want to show u = x - d - (y - d) + period m.
But this is clearly u = x - y + period m, which is our I.H. In the discrete case,
either the previous state was ovReady, and our result follows by the I.H. or the previous
state was not ovReady. In the latter case, we can use (...ovWait_prev...) and our inductive
hypothesis of nextSince (to eliminate initState) to show that the previous state must have
been ovReadyState m u0 l i n, with u = u0 - period m, and u = x. We then separately show
(the other half of this mutually inductive proof) that this combination of nextSince m t
and ovReadyState m u0 l implies that t + u0 = tw(m0, m) + period m, for some m0. Hence we
get t + u = tw(m0, m), and u = x from before, so t + x = tw(m0, m). Also, by
(...ovWait_prev...), we have much as in the base case, that on entering the state u = x
and y = period m. So u = x - y + period m holds. For ovReady: The base case fails to match,
the delay inductive case fails also because ovReady can't delay by progress [salvaged?],
and we can't go from ovWait to ovReady by a delay. So we're left with the discrete inductive
case, where the parameter t for next since is the same across both states. By
(...ovReady_prev...) then we show that the previous state was ovWaitState m u x 0.
Note the parameter y must be 0 so that the transition is enabled. But we also have by our
mutually inductive I.H. that u = x - y + period m, in this case y = 0, so we have
u = x + period m. So t + u = t + x + period m. But we know again by our mutual I.H.
that t + x = tw(m0, m). And so t + u = tw(m0, m) + period m as required.*)

(** ovReadyN applied to three expressions is ovReady of them.*)
Lemma ovReadyN_bisim (e1 e2 e3 : Exp) : ovReadyN $( [e1, e2, e3] )$ ~p~ ovReady e1 e2 e3.
Proof. unfold_app_bisim. apply bisim_refl. Qed.

(** Of two bisimilar ovWait, the second with a well-formed position timer, first parameters
that evaluate agree once the period of the mode is subtracted.*)
Local Lemma ovWait_bisim_first_val (m1 m2 : Mode) u1 x1 y1 u2 x2 y2 t tu1 tu2 :
  ovWait (eBase (baseMode m1)) u1 x1 y1 ~p~ ovWait (eBase (baseMode m2)) u2 x2 y2 ->
  evalExpFunTime y2 = Some t ->
  evalExpFunTime u1 = Some tu1 -> evalExpFunTime u2 = Some tu2 ->
  time tu1 -nn- time (period m1) = time tu2 -nn- time (period m1).
Proof.
  intros B E E1 E2.
  assert (EM : m2 = m1)
    by exact (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _ E (bisim_symm _ _ B))).
  subst m2.
  destruct (ovWait_bisim_pos_timeout _ _ _ _ _ _ _ _ _ B E) as [x1' [y1' [x2' [y2' [B' E']]]]].
  assert (S1 : exists q, ovWait (eBase (baseMode m1)) u2 x2' y2' -PA-
    inAct chanPos [basePosition origin] -PA> q).
  { eexists. unfold ovWait. apply stepDpChoiceL. apply stepDpChoiceR.
    apply stepDpTimeOut; [ | exact E']. apply stepDpIn. typed_vals. }
  destruct S1 as [q S1].
  destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ B') S1) as [r [R BR]].
  unfold ovWait in S1, R. invert_disc_prefixes. clean_proc_hyp BR.
  rewrite (subExp_eval_id _ u2 _ E2) in BR. rewrite (subExp_eval_id _ u1 _ E1) in BR.
  pose proof (bisim_trans _ _ _ (bisim_symm _ _ (ovReadyN_bisim _ _ _))
    (bisim_trans _ _ _ BR (ovReadyN_bisim _ _ _))) as BR'.
  assert (S2 : exists q2, ovReady (eBase (baseMode m1)) u2 (eBase (basePosition origin)) -PA-
    outAct chanOutProc [baseMode m1, basePosition origin] -PA> q2)
    by (eexists; unfold ovReady; apply stepDpOut; repeat constructor).
  destruct S2 as [q2 S2].
  destruct (bisim_step_disc _ _ _ _ BR' S2) as [q1 [S1' BQ]].
  destruct (ovReady_step_ovWait _ _ _ _ _ S2) as [_ W2].
  destruct (ovReady_step_ovWait _ _ _ _ _ S1') as [_ W1].
  pose proof (bisim_trans _ _ _ (bisim_symm _ _ W1)
    (bisim_trans _ _ _ (bisim_symm _ _ BQ) W2)) as BW.
  lets EX : ovWait_bisim_pause_timer BW (evalExpFunTime_subtract_period m1 u2 tu2 E2).
  rewrite (evalExpFunTime_subtract_period m1 u1 tu1 E1) in EX. injection EX as EX. exact EX.
Qed.

(** Out of init, the overlap component waits for the same mode, with its position timer zero, its
pause timer the wait time of a change and a period, and its first parameter equal to the pause
timer up to the period.*)
Lemma init_ovWait_timers_net m m' t' x y i n n' a :
  initStateNet m i n -> ovWaitStateNet m' t' x y i n' -> n -NA- a -NA> n' ->
  m = m' /\ y = zeroTime /\
  (exists (m0 : Mode) (pr : m0 -mtr-> m),
    nonneg (time x) = nonneg (time (waitTime m0 m pr)) + nonneg (time (period m))) /\
  time t' -nn- time (period m) = time x -nn- time (period m).
Proof.
  intros I OW S. net_state_destr I p1 p2 p3 l h k E.
  net_state_destr OW p1' p2' p3' l' h' k' E'.
  lets T : triple_disc_net S E E'. destruct T as [_ [[EQ | [b B]] _]].
  - (* the overlap component cannot be both *)
    subst p2'. exfalso.
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ OW) I) as C. ovWait_bisim_contra C.
  - (* init read the current mode and set both timers *)
    destruct (bisim_step_disc _ _ _ _ I B) as [q [SQ BQ]].
    unfold init in SQ. invert_disc_prefixes. explicit_typed_input. clean_proc_hyp BQ.
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ (ovWaitN_bisim _ _ _))
      (bisim_trans _ _ _ (bisim_symm _ _ BQ) OW)) as BW.
    pose proof (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _ (evalExpFunTime_time zeroTime) BW))
      as EM.
    subst m'.
    lets EY : ovWait_bisim_pos_timer BW (evalExpFunTime_time y).
    rewrite evalExpFunTime_time in EY. injection EY as EY.
    lets EX : ovWait_bisim_pause_timer BW (evalExpFunTime_time x).
    lets FV : ovWait_bisim_first_val BW (evalExpFunTime_time y) EX (evalExpFunTime_time t').
    split; [reflexivity | split; [symmetry; exact EY | split; [ | symmetry; exact FV]]].
    (* the pause timer: the wait time from the mode read to m, and a period *)
    unfold evalExpFunTime in EX. cbn [evalExpFun] in EX.
    match type of EX with context [modeTransRelOpt ?m0 _] =>
      destruct (modeTransRelOpt m0 m) as [pr | ]; cbn [option_map] in EX; [ | discriminate];
      apply (ex_intro _ m0); apply (ex_intro _ pr) end.
    rewrite !evalBaseNonnegFun_time in EX. destruct (period m) as [[pp pn]].
    cbn in EX. injection EX as EX. subst x. reflexivity.
Qed.

(** The wait time of a change is at least its warning part: the message latency, the larger of
the adaptation notification time and the maximal transition time, and the wait surplus.*)
Local Lemma waitTime_lower m1 m2 pr :
  msgLatency + Rmax adaptNotif transMax + waitSurplus <= waitTime m1 m2 pr.
Proof.
  assert (DW : forall d : Delay, nonneg (time (delToTime d)) = pos (delay d))
    by (intros [[r rp]]; reflexivity).
  unfold waitTime. rewrite timeMax_RMax. eapply Rle_trans; [ | apply Rmax_r].
  simpl. rewrite DW. apply Rle_refl.
Qed.

(** Bisimilar ovReady are for the same mode.*)
Lemma ovReady_bisim_mode (m1 m2 : Mode) u1 u2 (l1 l2 : Position) :
  ovReady (eBase (baseMode m1)) u1 (eBase (basePosition l1)) ~p~
  ovReady (eBase (baseMode m2)) u2 (eBase (basePosition l2)) -> m1 = m2.
Proof.
  intro B.
  assert (S1 : exists q, ovReady (eBase (baseMode m1)) u1 (eBase (basePosition l1)) -PA-
    outAct chanOutProc [baseMode m1, basePosition l1] -PA> q)
    by (eexists; unfold ovReady; apply stepDpOut; repeat constructor).
  destruct S1 as [q S1]. destruct (bisim_step_disc _ _ _ _ B S1) as [q2 [S2 _]].
  unfold ovReady in S2. invert_disc_prefixes. output_values. reflexivity.
Qed.

(** Two ovWait states of entity i are for one mode, with first parameters equal up to its
period.*)
Local Lemma ovWait_states_first_eq m1 m2 u1 u2 x1 x2 y1 y2 i n :
  ovWaitStateNet m1 u1 x1 y1 i n -> ovWaitStateNet m2 u2 x2 y2 i n ->
  m1 = m2 /\ time u1 -nn- time (period m1) = time u2 -nn- time (period m1).
Proof.
  intros W1 W2. pose proof (overlap_states_bisim_net _ _ _ _ W1 W2) as B.
  split; [exact (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _ (evalExpFunTime_time y1) B)) | ].
  exact (ovWait_bisim_first_val _ _ _ _ _ _ _ _ _ _ _ B (evalExpFunTime_time y2)
    (evalExpFunTime_time u1) (evalExpFunTime_time u2)).
Qed.

(** Two ovReady states of entity i are for one mode, with timers equal up to its period.*)
Local Lemma ovReady_states_timer_eq m1 m2 u1 u2 l1 l2 i n :
  ovReadyStateNet m1 u1 l1 i n -> ovReadyStateNet m2 u2 l2 i n ->
  m1 = m2 /\ time u1 -nn- time (period m1) = time u2 -nn- time (period m1).
Proof.
  intros R1 R2. pose proof (overlap_states_bisim_net _ _ _ _ R1 R2) as B.
  pose proof (ovReady_bisim_mode _ _ _ _ _ _ B) as EM. subst m2.
  split; [reflexivity | exact (ovReady_bisim_timer _ _ _ _ _ B)].
Qed.

(** A discrete step of the network, seen at the overlap component of entity i: the component
stays as it is or steps.*)
Lemma overlap_disc_net_cases (X : ProcTerm -> Prop) i n n' a :
  reachableProtNet n -> n -NA- a -NA> n' -> liftEntNet (liftProcEnt (liftOverlap X)) i n' ->
  exists p p', overlapState p /\ (p = p' \/ exists b, p -PA- b -PA> p') /\
    (forall Z, liftEntNet (liftProcEnt (liftOverlap Z)) i n <-> Z p) /\
    (forall Z, liftEntNet (liftProcEnt (liftOverlap Z)) i n' <-> Z p').
Proof.
  intros R S Q. net_state_destr Q p1' p2' p3' l' h' k' E'.
  destruct (link_net_ent_disc_bkwd _ _ _ _ _ S E') as [e [E _]].
  destruct e as [q l h k]. lets PS : reachableProtNet_triple R E.
  inversion PS as [p1 p2 p3 BS OS LS]; subst q.
  lets T : triple_disc_net S E E'. destruct T as [_ [T2 _]].
  exists p2 p2'. split; [exact OS | split; [exact T2 | ]].
  split; intro Z; split; intro H;
    first [net_state_ent H E; exact H | net_state_ent H E'; exact H
      | net_state_intro E; exact H | net_state_intro E'; exact H].
Qed.

(** A step into ovReady from a nextSince state is a position read of ovWait, whose position
timer had run out and whose first parameter is the timer of ovReady, up to the period.*)
Local Lemma nextSince_step_ready m (u : Time) l p p' b :
  nextSinceState p -> p -PA- b -PA> p' -> ovReadyState m u l p' ->
  exists (t x : Time), ovWaitState m t x zeroTime p /\
    time t -nn- time (period m) = time u -nn- time (period m).
Proof.
  intros NS T R.
  destruct NS as [m0 t0 x0 y0 H | m0 t0 l0 H | m0 H | m0 H];
    destruct (bisim_step_disc _ _ _ _ H T) as [q [TQ BQ]];
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ BQ) R) as BT;
    unfold ovWait, ovReady, switchBc, switchCurr in TQ; invert_disc_prefixes;
    explicit_typed_input; clean_proc_hyp BT;
    try solve [exfalso; unfold_app_hyp_l BT; prot_outProc_in_not_body; refute_by_chan BT].
  (* the position read, into ovReady m0 t0 *)
  match goal with [G : evalExpFunTime _ = Some zeroTime |- _] =>
    rewrite evalExpFunTime_time in G; injection G as G; subst y0 end.
  pose proof (bisim_trans _ _ _ (bisim_symm _ _ (ovReadyN_bisim _ _ _)) BT) as BR.
  pose proof (ovReady_bisim_mode _ _ _ _ _ _ BR) as EM. subst m0.
  exists t0 x0. split; [exact H | exact (ovReady_bisim_timer _ _ _ _ _ BR)].
Qed.

(** Back across a delay into ovWait, entity i was in ovWait for the same mode and first
parameter, with its position timer longer by the delay and its pause timer longer by at most
the delay.*)
Local Lemma ovWait_del_bkwd_net_le n n' d m t x y i :
  overlapStateNet i n -> n -ND- d -ND> n' -> ovWaitStateNet m t x y i n' ->
  exists (x0 : Time), ovWaitStateNet m t x0 (delToTime (y +dt+ d)) i n /\ x0 <= x + d.
Proof.
  intros OS D OW. net_state_destr OS p1 p2 p3 l h k E.
  net_state_destr OW p1' p2' p3' l' h' k' E'.
  lets T : triple_del_net D E E'. destruct T as [_ [D2 _]].
  lets EDEL : link_net_ent_delW D E' E.
  destruct (ovWait_timers_del_bkwd _ _ _ _ _ _ _ OS D2 OW) as [SP | [x0 [OW0 XE]]].
  - exfalso. eapply ent_del_pos_sort_not; [exact EDEL | ].
    apply sortParCompR. apply sortParCompL. exact SP.
  - exists x0. split; [net_state_intro E; exact OW0 | ].
    destruct (Rlt_le_dec x0 d) as [LT | GE]; [pose proof (cond_nonneg (time x)); lra | ].
    rewrite XE; [simpl; lra | ].
    (* the pause timer has not run out within the delay *)
    intro SX. apply (bisim_sort_iff _ _ _ _ OW0 (ex_intro _ _ D2)) in SX.
    apply ovWait_sort_pause in SX. destruct SX as [t3 [E3 LT]].
    rewrite evalExpFunTime_time in E3. injection E3 as E3. subst t3. lra.
Qed.

(** While entity i is pending, the first parameter of its wait and the timer of its ovReady,
less the period, are at least the warning part of a wait time.*)
Local Lemma pending_timers_above i n p : pending i n p ->
  (forall m u x y, ovWaitStateNet m u x y i n ->
     msgLatency + Rmax adaptNotif transMax + waitSurplus <= time u -nn- time (period m)) /\
  (forall m u l, ovReadyStateNet m u l i n ->
     msgLatency + Rmax adaptNotif transMax + waitSurplus <= time u -nn- time (period m)).
Proof.
  intro PE.
  induction PE as [a n n' p w m0 t0 x0 y0 IS OW | a n n' p w m0 t0 x0 y0 PE IH OW OW'
    | a n n' p w m0 l0 t0 x0 y0 PE IH OW OR | a n n' p w m0 l0 t0 PE IH OR OR'];
    split; intros m u.
  - (* init has just set the pause timer to the wait time and a period *)
    intros x y Q.
    destruct (init_ovWait_timers_net _ _ _ _ _ _ _ _ _ IS Q w) as [EM [_ [[m1 [pr XV]] FV]]].
    subst m0. rewrite FV.
    pose proof (subNonnegTot_le_Rminus (time x) (time (period m))).
    pose proof (waitTime_lower m1 m pr). lra.
  - intros l Q. exfalso. eapply ovReady_ovWait_bisim_not.
    exact (overlap_states_bisim_net _ _ _ _ OW Q).
  - intros x y Q. destruct (ovWait_states_first_eq _ _ _ _ _ _ _ _ _ _ Q OW') as [EM FV].
    subst m0. rewrite FV. exact (proj1 IH _ _ _ _ OW).
  - intros l Q. exfalso. eapply ovReady_ovWait_bisim_not.
    exact (overlap_states_bisim_net _ _ _ _ OW' Q).
  - intros x y Q. exfalso. eapply ovReady_ovWait_bisim_not.
    exact (overlap_states_bisim_net _ _ _ _ Q OR).
  - (* the position read: ovReady has the first parameter of the wait as its timer *)
    intros l Q. destruct (ovReady_states_timer_eq _ _ _ _ _ _ _ _ Q OR) as [EM FV].
    subst m0. rewrite FV. exact (proj1 IH _ _ _ _ OW).
  - intros x y Q. exfalso. eapply ovReady_ovWait_bisim_not.
    exact (overlap_states_bisim_net _ _ _ _ Q OR').
  - intros l Q. destruct (ovReady_states_timer_eq _ _ _ _ _ _ _ _ Q OR') as [EM FV].
    subst m0. rewrite FV. exact (proj2 IH _ _ _ OR).
Qed.

(** t and the time the overlap component of entity i has left before it pauses add up to at
least W: in ovWait, its pause timer, and its first parameter less the period and its position
timer; in ovReady, its timer less the period; in switchBc and switchCurr, nothing.*)
Local Definition ovTimersAbove (m : Mode) (W t : R) (i : nat) (n : Network) : Prop :=
  (forall u x y, ovWaitStateNet m u x y i n ->
     W <= t + x /\ W <= t + (time u -nn- time (period m)) + y) /\
  (forall u l, ovReadyStateNet m u l i n -> W <= t + (time u -nn- time (period m))) /\
  (switchBcStateNet m i n -> W <= t) /\ (switchCurrStateNet i n -> W <= t).

(** Across the broadcast of ovReady, a bound on t and its timer less the period becomes the
bounds of ovTimersAbove on the wait it starts.*)
Local Lemma broadcast_timers_above m W (t : R) t0 l u x y i n n' a :
  reachableProtNet n -> n -NA- a -NA> n' ->
  ovReadyStateNet m t0 l i n -> ovWaitStateNet m u x y i n' ->
  W <= t + (time t0 -nn- time (period m)) ->
  W <= t + x /\ W <= t + (time u -nn- time (period m)) + y.
Proof.
  intros R S OR Q L.
  destruct (overlap_disc_net_cases _ _ _ _ _ R S Q) as [p2 [p2' [_ [[EQ | [b B]] [V V']]]]].
  - exfalso. subst p2'. eapply ovReady_ovWait_bisim_not.
    exact (bisim_trans _ _ _ (bisim_symm _ _ (proj1 (V' _) Q)) (proj1 (V _) OR)).
  - destruct (bisim_step_disc _ _ _ _ (proj1 (V _) OR) B) as [q [TQ BQ]].
    destruct (ovReady_step_ovWait _ _ _ _ _ TQ) as [_ BW].
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ (proj1 (V' _) Q))
      (bisim_trans _ _ _ BQ BW)) as BB.
    pose proof (evalExpFunTime_subtract_period m _ _ (evalExpFunTime_time t0)) as ET.
    lets EX : ovWait_bisim_pause_timer BB ET.
    lets EY : ovWait_bisim_pos_timer BB (evalExpFunTime_period m).
    lets FV : ovWait_bisim_first_val BB (evalExpFunTime_period m) (evalExpFunTime_time u) ET.
    rewrite evalExpFunTime_time in EX, EY. injection EX as EX. injection EY as EY. subst x y.
    cbn [time] in FV |- *. rewrite FV.
    pose proof (subNonnegTot_le_Rminus (time t0 -nn- time (period m)) (time (period m))).
    split; lra.
Qed.

(** Just after the broadcast that makes entity i nextSince m, ovTimersAbove holds of zero and the
warning part of a wait time.*)
Local Lemma ovTimersAbove_base m t0 l t' x' y' i n n' a (p : reachableProtNet n) :
  n -NA- a -NA> n' -> pending i n p -> ovReadyStateNet m t0 l i n ->
  ovWaitStateNet m t' x' y' i n' ->
  ovTimersAbove m (msgLatency + Rmax adaptNotif transMax + waitSurplus) 0 i n'.
Proof.
  intros S PE OR OW. pose proof (proj2 (pending_timers_above _ _ _ PE) _ _ _ OR) as L.
  split; [intros u x y Q; apply (broadcast_timers_above _ _ _ _ _ _ _ _ _ _ _ _ p S OR Q); lra | ].
  (* entity i is in ovWait, so not in ovReady, switchBc or switchCurr *)
  split; [intros u l' Q | split; intro Q]; exfalso;
    pose proof (overlap_states_bisim_net _ _ _ _ OW Q) as BT; ovWait_bisim_contra BT.
Qed.

(** A discrete step into a nextSince state keeps ovTimersAbove of an entity nextSince m t.*)
Local Lemma ovTimersAbove_disc m W t i n n' a (p : reachableProtNet n) :
  n -NA- a -NA> n' -> nextSince m t i n p -> nextSinceStateNet i n' ->
  ovTimersAbove m W t i n -> ovTimersAbove m W t i n'.
Proof.
  intros S NS NSS [HW [HR [HB HC]]].
  pose proof (nextSince_rel_state _ _ _ _ _ NS) as NS0.
  split; [ | split; [ | split]].
  - (* ovWait: waiting already, or the broadcast of ovReady *)
    intros u x y Q.
    destruct (ovWait_prev_net _ _ _ _ _ _ _ _ p Q S) as [Q0 | [[t0 [l0 [R0 _]]] | IS]].
    + exact (HW _ _ _ Q0).
    + exact (broadcast_timers_above _ _ _ _ _ _ _ _ _ _ _ _ p S R0 Q (HR _ _ R0)).
    + exfalso. exact (init_nextSince_net_not _ _ _ IS NS0).
  - (* ovReady: ready already, or the position read of ovWait *)
    intros u l Q.
    destruct (overlap_disc_net_cases _ _ _ _ _ p S Q) as [p2 [p2' [_ [[EQ | [b B]] [V V']]]]].
    + subst p2'. exact (HR _ _ (proj2 (V _) (proj1 (V' _) Q))).
    + destruct (nextSince_step_ready _ _ _ _ _ _ (proj1 (V _) NS0) B (proj1 (V' _) Q))
        as [t0 [x0 [W0 FV]]].
      pose proof (proj2 (HW _ _ _ (proj2 (V _) W0))) as L.
      assert (Z0 : nonneg (time zeroTime) = 0) by reflexivity.
      rewrite Z0, FV in L. lra.
  - (* switchBc: there already, or the pause of ovWait, whose pause timer had run out *)
    intro Q.
    destruct (overlap_disc_net_cases _ _ _ _ _ p S Q) as [p2 [p2' [OS [[EQ | [b B]] [V V']]]]].
    + subst p2'. exact (HB (proj2 (V _) (proj1 (V' _) Q))).
    + destruct (switchBc_prev _ _ _ _ B OS (proj1 (V' _) Q)) as [e2 [e4 WE]].
      (* the nextSince state of entity i is that wait, with its pause timer run out *)
      destruct (proj1 (V _) NS0) as [m0 t0 x0 y0 W0 | m0 t0 l0 S0 | m0 S0 | m0 S0];
        [ | exfalso; pose proof (bisim_trans _ _ _ (bisim_symm _ _ WE) S0) as BT;
            ovWait_bisim_contra BT ..].
      pose proof (bisim_trans _ _ _ (bisim_symm _ _ W0) WE) as BW.
      lets EX : ovWait_bisim_pause_timer BW (evalExpFunTime_time zeroTime).
      rewrite evalExpFunTime_time in EX. injection EX as EX. subst x0.
      pose proof (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _ (evalExpFunTime_time y0) BW))
        as EM. subst m0.
      pose proof (proj1 (HW _ _ _ (proj2 (V _) W0))) as L.
      assert (Z0 : nonneg (time zeroTime) = 0) by reflexivity. rewrite Z0 in L. lra.
  - (* switchCurr: there already, or the wake of switchBc *)
    intro Q.
    destruct (overlap_disc_net_cases _ _ _ _ _ p S Q) as [p2 [p2' [OS [[EQ | [b B]] [V V']]]]].
    + subst p2'. exact (HC (proj2 (V _) (proj1 (V' _) Q))).
    + destruct (switchCurr_prev _ _ _ B OS (proj1 (V' _) Q)) as [m0 S0].
      pose proof (proj2 (V _) S0) as S0n.
      rewrite <- (nextSince_switchBc_modeEq _ _ _ _ _ _ NS S0n) in S0n. exact (HB S0n).
Qed.

(** A delay keeps ovTimersAbove, with t later by the delay.*)
Local Lemma ovTimersAbove_del m W t i n n' (d : Delay) :
  reachableProtNet n -> n -ND- d -ND> n' -> ovTimersAbove m W t i n ->
  ovTimersAbove m W (t + d) i n'.
Proof.
  intros R D [HW [HR [HB HC]]]. pose proof (cond_pos (delay d)) as DP.
  split; [ | split; [ | split]].
  - intros u x y Q.
    destruct (reachableProtNet_del_prev _ _ _ _ _ R D Q) as [_ [OS _]].
    destruct (ovWait_del_bkwd_net_le _ _ _ _ _ _ _ _ OS D Q) as [x0 [Q0 LE]].
    destruct (HW _ _ _ Q0) as [L1 L2]. simpl in L2. split; lra.
  - intros u l Q.
    destruct (reachableProtNet_del_prev _ _ _ _ _ R D Q) as [_ [OS _]].
    pose proof (HR _ _ (ovReady_del_pres_bkwd_net _ _ _ _ _ _ _ OS D Q)). lra.
  - intro Q. destruct (reachableProtNet_del_prev _ _ _ _ _ R D Q) as [_ [OS _]].
    assert (Q0 : switchBcStateNet m i n)
      by (apply (overlap_del_bkwd_net _ _ _ _ _ OS D Q); intros m0 e2 e3 e4 B;
          ovWait_bisim_contra B).
    pose proof (HB Q0). lra.
  - intro Q. destruct (reachableProtNet_del_prev _ _ _ _ _ R D Q) as [_ [OS _]].
    assert (Q0 : switchCurrStateNet i n)
      by (apply (overlap_del_bkwd_net _ _ _ _ _ OS D Q); intros m0 e2 e3 e4 B;
          ovWait_bisim_contra B).
    pose proof (HC Q0). lra.
Qed.

(** While entity i is nextSince m t, ovTimersAbove holds of t and the warning part of a wait time.*)
Local Lemma nextSince_timers_above m t i n (p : reachableProtNet n) :
  nextSince m t i n p ->
  ovTimersAbove m (msgLatency + Rmax adaptNotif transMax + waitSurplus) t i n.
Proof.
  intro NS.
  induction NS as [a i n n' p w l t0 t' x y PE OR OW | a t i n n' p w NS IH NSS
    | d t i n n' p w NS IH].
  - exact (ovTimersAbove_base _ _ _ _ _ _ _ _ _ _ p w PE OR OW).
  - exact (ovTimersAbove_disc _ _ _ _ _ _ _ p w NS NSS IH).
  - exact (ovTimersAbove_del _ _ _ _ _ _ _ p w IH).
Qed.

(* If an entity is nextSince m t, and the same entity is in the state
switchBcState m, then we can show that mL + max AN trans < t.*)
Theorem nextSince_switchBc_lower (n : Network) (m : Mode) (i : nat)
  (t : Time) (p : reachableProtNet n) :
  nextSince m t i n p -> switchBcStateNet m i n ->
  msgLatency + Rmax adaptNotif transMax < t.
(**Proof: Induction on nextSince. BaseType case fails. Delay follows by monotonicity of t with
nextSince, as does the discrete case where the previous state is still switchBCState. So
the only case of any complexity is the discrete inductive case where the previous state was
not a switchBcState m. In which case we can show that it must be ovWaitState m u 0 y for
some u and y (...switchBc_prev...). We then have by (nextSince_ovWait_time), with x = 0,
that t + 0 = tw(m0, m), which simplifies to t = tw(m0, m). We can then expand tw to max
(mL + max(AN, trans) + Dw) (ts m1 m2) which, due to a strictly positive Dw, is greater
than mL + max AN trans as required.*)
Proof.
  intros NS SB. destruct (nextSince_timers_above _ _ _ _ _ NS) as [_ [_ [HB _]]].
  pose proof (HB SB). pose proof (cond_pos (delay waitSurplus)). lra.
Qed.

(* If an entity is nextSince m t, and the same entity is in the state switchCurrState m,
then we can show that mL + max AN trans < t.*)
Theorem nextSince_switchCurr_lower (n : Network) (m : Mode) (i : nat)
  (t : Time) (p : reachableProtNet n) :
  nextSince m t i n p -> switchCurrStateNet i n ->
  msgLatency + Rmax adaptNotif transMax < t.
(**Proof: SIMILAR TO ANALOGOUS PROOF FOR SWITCHBC- SHARED TACTICS?
Induction on nextSince and case analysis on switchCurrState. The base case fails.
For the inductive case, we case analyse the previous state for the predicate switchCurrState.
 If this was true, then by the I.H. the t parameter in that state exceeds the lower bound, 
and so, by monotonicity of nextSince in both delay & discrete cases, so will the t' in this 
state. Otherwise, the previous state is not switchCurrState m. In which case we can show 
that it must be switchBcState m (...switchCurr_prev...). We then prove a similar result for 
this (nextSince_switchBc_lower) & since the t parameter is the same from the last state to 
this one because our transition is discrete, that result carries forward.*)
Proof.
  intros NS SC. destruct (nextSince_timers_above _ _ _ _ _ NS) as [_ [_ [_ HC]]].
  pose proof (HC SC). pose proof (cond_pos (delay waitSurplus)). lra.
Qed.

End NAROvlpTime.
