(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Reals Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lra.
Require Import ComhCoq.lib.Extras.LibTactics.

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
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults.
Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.protocol.ProtocolBridge.

(*IDEA: MIGRATE SOME OF THE CONTENTS OF THE FILE OVER VARIUOS NAB (NET-AUX-BASICS)
PREFIXED FILES, THEN *EXPORT* THEM HERE, SO THAT THIS FILE JUST ACTS AS A
HUB RELAYING THE CONTENTS OF THOSE FILES. WHY? IT'S GETTING JOLLY BIG!*)

(********************************* Some basic definitions *********************************)

(** Initial and reachable networks for the protocol are the language's, with the protocol
process as the seed: Definitions 6.1 and 6.2 (p.133).*)
Notation initialProtNet := (initialNet procProtocol).
Notation reachableProtNet := (reachableNet procProtocol).

(** In a reachable network, every entity's software is reachable from the protocol process,
and so is a protocol triple.*)
Lemma reachable_net_prot : forall (n : Network) (i : nat)
  (p : ProcTerm) (l : Position) (h : Interface) (k : ModeState),
  reachableProtNet n -> [|p, l, h, k|] @ i .: n ->
  reachableProt p.
Proof.
  intros n i p l h k R E. apply reachableProt_reachableFrom.
  eapply reachableNet_proc; eassumption.
Qed.

Lemma reachableProtNet_triple n p l h k i :
  reachableProtNet n -> [|p, l, h, k|] @ i .: n -> protocolState p.
Proof.
  intros R E. apply reachableProt_triple. eapply reachable_net_prot; eassumption.
Qed.

(********************************* Steps to a component *********************************)
(** The language takes a network step down to the components of an entity's software, for
any number of them (net_disc_comps and its kin in NetworkLanguage.v). Here the software is
the protocol's triple, and a network state predicate says that one component of entity i's
triple satisfies a predicate. The results below take a step to the components of a triple,
and the tactics take a state predicate apart into the entity and the component's predicate
and put it back, so that a result about a component lifts to the network in a few lines.*)

(** A discrete step, between entity i's triples before and after it: each component is
unchanged or stepped once.*)
Lemma triple_disc_net i n n' a p1 p2 p3 p1' p2' p3' l l' h h' k k' :
  n -NA- a -NA> n' -> [|p1 $||$ p2 $||$ p3, l, h, k|] @ i .: n ->
  [|p1' $||$ p2' $||$ p3', l', h', k'|] @ i .: n' ->
  (p1 = p1' \/ exists b, p1 -PA- b -PA> p1') /\ (p2 = p2' \/ exists b, p2 -PA- b -PA> p2') /\
  (p3 = p3' \/ exists b, p3 -PA- b -PA> p3').
Proof.
  intros S E E'. change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in E.
  change (p1' $||$ p2' $||$ p3') with (parAll p1' [p2', p3']) in E'.
  lets F : net_disc_comps S E E'. specialize (F eq_refl). triple_pos.
  repeat split; assumption.
Qed.

(** A delay, between entity i's triples before and after it: each component delays by it.*)
Lemma triple_del_net i n n' d p1 p2 p3 p1' p2' p3' l l' h h' k k' :
  n -ND- d -ND> n' -> [|p1 $||$ p2 $||$ p3, l, h, k|] @ i .: n ->
  [|p1' $||$ p2' $||$ p3', l', h', k'|] @ i .: n' ->
  p1 -PD- d -PD> p1' /\ p2 -PD- d -PD> p2' /\ p3 -PD- d -PD> p3'.
Proof.
  intros D E E'. change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in E.
  change (p1' $||$ p2' $||$ p3') with (parAll p1' [p2', p3']) in E'.
  lets F : net_del_comps D E E'. specialize (F eq_refl). triple_pos.
  repeat split; assumption.
Qed.

(** A delay, forward from entity i's triple: a triple, each component delayed by it.*)
Lemma triple_del_fwd_net i n n' d p1 p2 p3 l h k :
  n -ND- d -ND> n' -> [|p1 $||$ p2 $||$ p3, l, h, k|] @ i .: n ->
  exists p1' p2' p3' l' h' k', [|p1' $||$ p2' $||$ p3', l', h', k'|] @ i .: n' /\
  p1 -PD- d -PD> p1' /\ p2 -PD- d -PD> p2' /\ p3 -PD- d -PD> p3'.
Proof.
  intros D E. change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in E.
  destruct (net_del_comps_fwd _ _ _ _ _ _ _ _ _ D E) as [p1' [qs' [l' [h' [k' [E' F]]]]]].
  positions_inv. do 6 eexists. split; [exact E' | ]. repeat split; assumption.
Qed.

(** Takes H : X_Net i n apart, for a network state predicate lifted from a predicate on one
component: E : [|p1 $||$ p2 $||$ p3, l, h, k|] @ i .: n is the entity, and H becomes the
component's predicate.*)
Ltac net_state_destr H p1 p2 p3 l h k E :=
  let e := fresh "e" in let P := fresh "P" in let p := fresh "p" in
  let H' := fresh H in
  destruct H as [e P E]; inversion P as [p l h k H]; subst e; clear P;
  inversion H as [p1 p2 p3 H']; subst p; clear H; rename H' into H.

(** From H : X_Net i n and the entity E : [|p1 $||$ p2 $||$ p3, l, h, k|] @ i .: n, the
component's predicate, as H.*)
Ltac net_state_ent H E :=
  let H' := fresh H in lets H' : liftEntNet_ent H E; clear H;
  inversion H' as [? ? ? ? H]; subst; clear H';
  let H'' := fresh H in inversion H as [? ? ? H'']; subst; clear H; rename H'' into H.

(** Proves a network state predicate of the entity E : [|p1 $||$ p2 $||$ p3, l, h, k|] @ i .: n,
leaving the component's predicate as the goal.*)
Ltac net_state_intro E :=
  eapply lenWitness; [ | exact E]; constructor; constructor.

(********************************* Lifting Protocol Predicates *********************************)

(*----------------Simple Lifted Predicates----------------*)

(**Broadcast*)
Definition bcWaitStateNet m x := liftEntNet (bcWaitStateEnt m x).
Definition sleepingStateNet := liftEntNet sleepingStateEnt.
Definition bcReadyStateNet m l := liftEntNet (bcReadyStateEnt m l).


(**Overlap*)
Definition dormantStateNet := liftEntNet dormantStateEnt.
Definition tfsStartStateNet := liftEntNet tfsStartStateEnt.
Definition initStateNet m := liftEntNet (initStateEnt m).
Definition ovWaitStateNet m t x y := liftEntNet (ovWaitStateEnt m t x y).
Definition ovWaitTypedNet := liftEntNet ovWaitTypedEnt.
Definition ovReadyStateNet m t l := liftEntNet (ovReadyStateEnt m t l).
Definition switchCurrStateNet := liftEntNet switchCurrStateEnt.
Definition switchListenStateNet := liftEntNet switchListenStateEnt.
Definition switchBcStateNet m := liftEntNet (switchBcStateEnt m).
Definition tfsCurrStateNet := liftEntNet tfsCurrStateEnt.
Definition tfsBcStateNet := liftEntNet tfsBcStateEnt.
Definition tfsListenStateNet := liftEntNet tfsListenStateEnt.
Definition pausedStateNet := liftEntNet pausedStateEnt.
Definition tfsNextStateNet m := liftEntNet (tfsNextStateEnt m).

(**Listener*)
Definition listeningStateNet := liftEntNet listeningStateEnt.
Definition currCompStateNet m'' r := liftEntNet (currCompStateEnt m'' r).
Definition badOvlpStateNet := liftEntNet badOvlpStateEnt.
Definition rangeBadStateNet m := liftEntNet (rangeBadStateEnt m).
Definition currEqStateNet m m'' := liftEntNet (currEqStateEnt m m'').


(*----------------Compound Lifted Predicates----------------*)


(**Broadcast*)
Definition broadcastStateNet :=  liftEntNet broadcastStateEnt.

(**Overlap*)
Definition overlapStateNet := liftEntNet overlapStateEnt.
Definition tfsStateNet := liftEntNet tfsStateEnt.
Definition nextSinceStateNet := liftEntNet (nextSinceStateEnt).
Definition switchStateNet := liftEntNet switchStateEnt.

(**Listener*)
Definition listenerStateNet := liftEntNet listenerStateEnt.
Definition ovAbortStateNet := liftEntNet ovAbortStateEnt.


(********************************* State Predicate Results *********************************)

(** In a reachable network, entity i's components are in broadcast, overlap and listener
states. The tracking results below assume these states rather than reachability, so they
hold of any network whose entity i is in them; a reachable network is, through this
lemma and the next.*)
Lemma reachableProtNet_states n e i :
  reachableProtNet n -> e @ i .: n ->
  broadcastStateNet i n /\ overlapStateNet i n /\ listenerStateNet i n.
Proof.
  intros R E. destruct e as [p l h k]. lets PS : reachableProtNet_triple R E.
  inversion PS as [p1 p2 p3 BS OS LS]; subst.
  split; [ | split]; (eapply lenWitness; [ | exact E]); constructor; constructor; assumption.
Qed.

(** Before a delay of a reachable network into a network where entity i is in some state,
entity i's components were in broadcast, overlap and listener states.*)
Lemma reachableProtNet_del_prev n n' d i (X : Entity -> Prop) :
  reachableProtNet n -> n -ND- d -ND> n' -> liftEntNet X i n' ->
  broadcastStateNet i n /\ overlapStateNet i n /\ listenerStateNet i n.
Proof.
  intros R D L. destruct L as [e' _ E'].
  destruct (link_net_ent_del_bkwd _ _ _ _ _ D E') as [e [E _]].
  eapply reachableProtNet_states; eassumption.
Qed.

(** A delay, back to the overlap component: an overlap state Z that no ovWait is bisimilar
to was the component's state before the delay, since every other overlap state delays only
to itself (overlap_del_bkwd). The component is an overlap state before the delay, as it is
in a reachable network; so for every result below that assumes it.*)
Lemma overlap_del_bkwd_net (Z : ProcTerm) i n n' d :
  overlapStateNet i n -> n -ND- d -ND> n' ->
  liftEntNet (liftProcEnt (liftOverlap (fun p => p ~p~ Z))) i n' ->
  (forall m e2 e3 e4, ovWait m e2 e3 e4 ~p~ Z -> False) ->
  liftEntNet (liftProcEnt (liftOverlap (fun p => p ~p~ Z))) i n.
Proof.
  intros OS D L NW. net_state_destr OS p1 p2 p3 l h k E.
  net_state_destr L p1' p2' p3' l' h' k' E'.
  lets T : triple_del_net D E E'. destruct T as [_ [D2 _]].
  net_state_intro E. eapply overlap_del_bkwd; eassumption.
Qed.

(* begin helpers for tfsStateNet_dec *)
From Stdlib Require Import Classical_Prop.
(* end helpers *)

Lemma tfsStateNet_dec : forall (i : nat) (n : Network), decidable (tfsStateNet i n).
Proof.
  intros i n. unfold decidable. apply Classical_Prop.classic.
Qed.
(**Proof: Obvious*)

Lemma tfsCurrNet_dec : forall (i : nat) (n : Network),
  decidable (tfsCurrStateNet i n).
Proof.
  intros i n. unfold decidable. apply Classical_Prop.classic.
Qed.
(**Proof: Obvious*)

(*Pre-requisite: some sort of lifting tactic*)
Lemma tfsCurrStateNet_bktrk_net : forall (n n' : Network) (i : nat) (a : ActDiscNet),
  reachableProtNet n -> tfsCurrStateNet i n' -> n -NA- a -NA> n' ->
  tfsCurrStateNet i n \/
  (exists m mF, exists p,
  tfsNextStateNet m i n /\ failSafe mF /\
  mState_in_net (<| m, mF, modeTransTime m mF p |>) i n'). Admitted. (*6*)
(**Proof: Lift Back tracking and inter component relationships*)  

(** A delay keeps the overlap component in tfsCurr, either way: tfsCurr delays only to
itself, and no overlap state but ovWait delays into anything else.*)
Lemma tfsCurrState_del_pres_net : forall (n n' : Network) (d : Delay) (i : nat),
  overlapStateNet i n -> n -ND- d -ND> n' ->
  (tfsCurrStateNet i n <-> tfsCurrStateNet i n').
Proof.
  intros n n' d i OS D. split; intro TC.
  - net_state_destr TC p1 p2 p3 l h k E. lets T : triple_del_fwd_net D E.
    destruct T as [p1' [p2' [p3' [l' [h' [k' [E' [_ [D2 _]]]]]]]]].
    net_state_intro E'. eapply bisim_del_pres; [del_self_body | exact TC | exact D2].
  - apply (overlap_del_bkwd_net tfsCurr _ _ _ _ OS D TC).
    intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
Qed.

(*An unstable mode state changes in a discrete transition only by the standard mode switch,
the mode switch to fail safe, or the overlap component aborting the mode change.*)
Lemma mState_switch_states : forall (n n' : Network) (i : nat)
  (a : ActDiscNet) (k k' : ModeState), reachableProtNet n -> unstable k -> k <> k' ->
  n -NA- a -NA> n' -> mState_in_net k i n -> mState_in_net k' i n' ->
  (tfsCurrStateNet i n /\ tfsBcStateNet i n') \/
  (switchCurrStateNet i n /\ switchListenStateNet i n') \/
  (ovAbortStateNet i n /\ dormantStateNet i n') \/
  (exists m, tfsNextStateNet m i n /\ tfsNextStateNet m i n').
Proof.
  intros n n' i a k k' R U NE S M M'.
  destruct M as [p l h E]. destruct M' as [p' l' h' E'].
  destruct (link_net_ent_disc _ _ _ _ _ _ S E E') as [EQ | [b B]].
  { injection EQ; intros; subst. contradiction NE; reflexivity. }
  destruct (mState_switch_states_ent _ _ _ _ _ _ _ _ _ (reachableNet_ent _ _ _ _ R E) U NE B)
    as [[A D] | [[A D] | [[A D] | [m [A D]]]]];
    [left | right; left | right; right; left | right; right; right; exists m];
    (split; [econstructor; [exact A | exact E] | econstructor; [exact D | exact E']]).
Qed.

(**Proof: The mState_in_net predicates can be taken apart to show that there's an entity in the network. Then because the
network is reachable, the software component of this entity is a protocolState process. Also, it can be shown from the semantics of
entities that the only law (what about init?) that changes the mode state is that in which the software component outputs on mCurr.
Brute force analysis of the possible states of each 3 components of the softare component show that the only matching cases for this are
the two disjuncts. That is, the only capability a protocol process has of writing on mCurr is from the overlap component in those specific
states.*)

(** A delay keeps the overlap component in a tfs state, either way, as for tfsCurr.*)
Lemma tfsState_del_pres_net : forall (n n' : Network) (i : nat) (d : Delay),
  overlapStateNet i n -> n -ND- d -ND> n' -> (tfsStateNet i n <-> tfsStateNet i n').
Proof.
  intros n n' i d OS D. split; intro TS.
  - net_state_destr TS p1 p2 p3 l h k E. lets T : triple_del_fwd_net D E.
    destruct T as [p1' [p2' [p3' [l' [h' [k' [E' [_ [D2 _]]]]]]]]].
    net_state_intro E'. eapply del_pres_tfsState; eassumption.
  - net_state_destr OS p1 p2 p3 l h k E. net_state_destr TS p1' p2' p3' l' h' k' E'.
    lets T : triple_del_net D E E'. destruct T as [_ [D2 _]].
    net_state_intro E.
    destruct TS as [T | m T | T | T | T];
      [apply tfsStaSt | apply (tfsNexSt _ m) | apply tfsCurSt | apply tfsBcSt | apply tfsLisSt];
      (eapply overlap_del_bkwd; [exact OS | exact D2 | exact T | ]);
      intros m0 e2 e3 e4 B; ovWait_bisim_contra B.
Qed.

Lemma switch_states_mState : forall (n n' : Network) (i : nat) (a : ActDiscNet)
  (m : Mode), reachableProtNet n -> n -NA- a -NA> n' -> switchCurrStateNet i n ->
  switchListenStateNet i n' -> nextModeNet m i n -> currModeNet m i n'.
Proof.
  intros n n' i a m R S SC SL NM.
  net_state_destr SC p1 p2 p3 l h k E.
  net_state_destr SL p1' p2' p3' l' h' k' E'.
  assert (NB : p2 <> p2').
  { intro EQ; subst p2'. lets D : switchCurr_mCurr_out SC.
    destruct (bisim_dae _ _ _ SL D) as [q T]. unfold switchListen in T. inversion T. }
  destruct (link_net_ent_disc _ _ _ _ _ _ S E E') as [EQ | [b B]].
  { injection EQ; intros; subst. contradiction NB; reflexivity. }
  (* switchCurr only writes on mCurr, and so the mode state takes the write *)
  assert (SW : forall b2, p2 -PA- b2 -PA> p2' -> b2 = chanMCurrWrite *!).
  { intros b2 T2. destruct (bisim_step_disc _ _ _ _ SC T2) as [q [TQ _]].
    unfold switchCurr in TQ. invert_disc_prefixes.
    match goal with [H : evalExpLists [] _ |- _] => inversion H end. reflexivity. }
  assert (ACT : forall b2, p2 -PA- b2 -PA> p2' -> entChanAct b2)
    by (intros b2 T2; rewrite (SW b2 T2); right; reflexivity).
  destruct (triple_disc_ent_chan 1 (reachableNet_ent _ _ _ _ R E) B eq_refl eq_refl ACT)
    as [EQ | B2]; [contradiction | ].
  destruct (ent_disc_proc_write _ _ _ _ _ _ _ _ _ B2) as [EQ | [c [T [CW _]]]];
    [contradiction | ].
  specialize (CW (SW c T)). inversion CW; subst.
  lets NM' : liftEntNet_ent NM E. simpl in NM'. injection NM' as NM'. subst.
  eapply lenWitness; [ | exact E']. reflexivity.
Qed.
(**Proof: Tracking shows us that the action must be tau, composed of an output from the software process on mCurr and an input
on the same by the mode state. Then it can be shown separately that an input on the mode state that is nextMode m yields a mode
state that it currMode m. Which can be lifted to currModeNet.*)

(** The action linking a change from switchCurr to switchListen is always a tau.*)
Lemma switchCurr_listen_trans_tau (n n' : Network) (a : ActDiscNet) (i : nat) :
  n -NA- a -NA> n' -> switchCurrStateNet i n -> switchListenStateNet i n' ->
  a = anTau.
Proof.
  intros S U V.
  destruct U as [e U1 U2]. destruct V as [e' V1 V2].
  destruct U1 as [p l h k P]. destruct V1 as [p' l' h' k' P'].
  eapply procNeq_tau_net; [exact U2 | exact V2 | exact S | ].
  intro EQ; subst p'.
  destruct P as [p1 p2 p3 Q].
  inversion P' as [p1' p2' p3' Q' EQ]; subst.
  lets D : switchCurr_mCurr_out Q.
  lets D' : bisim_dae Q' D.
  destruct D' as [q T]. unfold switchListen in T. inversion T.
Qed.

(*LOCAL TIDY*)

(* begin helpers for tfsStart_tfs_net *)
(** Lifts an overlap-component inclusion into tfsState (given by the
tfsState constructor C) through the entity and network lifting layers.*)
Ltac tfsStart_tfs_net_tac C :=
  let H := fresh "H" in let e := fresh "e" in
  let He := fresh "He" in let Hin := fresh "Hin" in
  intro H; destruct H as [e He Hin]; apply lenWitness with (e := e); [ | exact Hin];
  let p := fresh "p" in let l := fresh "l" in let h := fresh "h" in
  let k := fresh "k" in let Hp := fresh "Hp" in
  destruct He as [p l h k Hp]; constructor;
  let p1 := fresh "p1" in let p2 := fresh "p2" in let p3 := fresh "p3" in
  let Hq := fresh "Hq" in
  destruct Hp as [p1 p2 p3 Hq]; constructor; eapply C; exact Hq.
(* end helpers *)

Lemma tfsStart_tfs_net i n :
  tfsStartStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsStaSt.
Qed.

Lemma tfsNext_tfs_net m i n :
  tfsNextStateNet m i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsNexSt.
Qed.

Lemma tfsCurr_tfs_net i n :
  tfsCurrStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsCurSt.
Qed.

Lemma tfsBc_tfs_net i n :
  tfsBcStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsBcSt.
Qed.

Lemma tfsListen_tfs_net i n :
  tfsListenStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsLisSt.
Qed.

(** The following three tactics are mostly simply auxiliaries to the main
result of fwd_track_net_tac.*)
(*Applies eexists up to 5 times (or not at all) before applying t- until
the application works.*)
Ltac first_eexists_5 t := first [t | (do 1 eexists);t | (do 2 eexists);t |
  (do 3 eexists);t | (do 4 eexists);t | (do 5 eexists);t].
Ltac econstr_easssump := econstructor; eassumption.
Ltac first_ex_econ_eass := first_eexists_5 econstr_easssump.

(** RE is the entity level result upon which this tactic works. Essentially,
this tactic lifts RE from the entity to the network level. Note that the tactic
assumes a disjunctive goal of two branches and may not work otherwise.*)
Ltac fwd_track_net_tac RE :=
  let U := fresh in let U0 := fresh in
  (*Destruct a load of things and set up the link*)
  intros U U0; destruct U0;
  let e' := fresh "e'" in let b := fresh "b" in
  let LNE := fresh "LNE" in
  link_netentdiscfwd_tac e' b LNE;
  (*The case of equality of entities is easy, we just substitute.*)
  [subst; left | match goal with [LNE1 : _ -EA- b ->> e', e : Entity,
  H0 : _ ?e |- _] =>
  (*Apply an underlying (lower-level) result*)
  lets LOW : RE LNE1 H0;
  or_flat; ex_flat; [left | right] end];
  first_ex_econ_eass.

Lemma tfsStart_next_net n n' a i :
  n -NA- a -NA> n' -> tfsStartStateNet i n ->
  tfsStartStateNet i n' \/ exists m, tfsNextStateNet m i n'.
  fwd_track_net_tac tfsStart_next_ent. Qed.

Lemma tfsNext_next_net m n n' a i :
  n -NA- a -NA> n' -> tfsNextStateNet m i n ->
  tfsNextStateNet m i n' \/ tfsCurrStateNet i n'.
  fwd_track_net_tac tfsNext_next_ent. Qed.

Lemma tfsCurr_next_net n n' a i :
  n -NA- a -NA> n' -> tfsCurrStateNet i n ->
  tfsCurrStateNet i n' \/ tfsBcStateNet i n'.
  fwd_track_net_tac tfsCurr_next_ent. Qed.

Lemma tfsBc_next_net n n' a i :
  n -NA- a -NA> n' -> tfsBcStateNet i n ->
  tfsBcStateNet i n' \/ tfsListenStateNet i n'.
  fwd_track_net_tac tfsBc_next_ent. Qed.

Lemma tfsListen_next_net n n' a i :
  n -NA- a -NA> n' -> tfsListenStateNet i n ->
  tfsListenStateNet i n' \/ dormantStateNet i n'.
  fwd_track_net_tac tfsListen_next_ent. Qed.

Lemma rangeBad_next_net m m'' i n n' a : reachableProtNet n ->
  n -NA- a -NA> n' -> rangeBadStateNet m'' i n -> currModeNet m i n ->
  rangeBadStateNet m'' i n' \/ currEqStateNet m m'' i n'.
  (*Proof: If it wasn't for the currModeNet entanglement, you'd just be able
  to do: fwd_track_net_tac rangeBad_next_ent, but something else needs to be
  done to account for this extra little feature of the proof.*)
Proof.
  intros R S RB CM. destruct RB as [e RBe Ein].
  destruct (link_net_ent_disc_fwd n n' e i a S Ein) as [e' [E'in [Eq | [a' Ste]]]].
  - subst. left. econstructor; eassumption.
  - destruct (rangeBad_track_ent _ _ _ _ (reachableNet_ent _ _ _ _ R Ein) RBe Ste)
      as [RB' | CE].
    + left. econstructor; eassumption.
    + right. lets CM' : liftEntNet_ent CM Ein. simpl in CM'. rewrite CM' in CE.
      econstructor; eassumption.
Qed.

Lemma badOvlp_next_net i n n' a :
  n -NA- a -NA> n' -> badOvlpStateNet i n ->
  badOvlpStateNet i n' \/ listeningStateNet i n'.
Proof.
  intros TR B. destruct B as [e Be Ein].
  destruct (link_net_ent_disc_fwd n n' e i a TR Ein) as [e' [E'in [Eq | [a' Ste]]]].
  - subst. left. econstructor; eassumption.
  - destruct Be as [p l h k Bp]. destruct e' as [p' l' h' k'].
    destruct (link_ent_soft_disc p p' l l' h h' k k' a' Ste) as [Peq | [b Stp]].
    + subst. left. econstructor; [ | exact E'in]. constructor. exact Bp.
    + destruct Bp as [p1 p2 p3 B3].
      link_partripdiscex_tac Peq p1' p2' p3'.
      subst p'.
      link_partripdiscW3_tac Stp W. destruct W as [E3 | [a3 St3]].
      * subst. left. econstructor; [ | exact E'in]. constructor. constructor. exact B3.
      * right. econstructor; [ | exact E'in]. constructor. constructor.
        eapply badOvlp_next; eassumption.
Qed.
(*Proof: fwd_track_net_tac badOvlp_next_ent*)

Ltac netState_auto_pre := match goal with [U : [|_, _, _, _|] = _,
  U1 : _ $||$ _ $||$ _ = _ |- _] =>
  eapply lenWitness;[ | eassumption];
  rewrite <- U; eapply lifpe; rewrite <- U1 end; constructor.

(** Assume a network state predicate as the goal, and enough information in the
hypothesis to prove it: an entInNet, an equality between that entity and its
various components, and an equality between a process triple and the process of
that entity. Then this tactic should solve the goal.*)
Ltac netState_auto_tac :=
  netState_auto_pre; eassumption.

Lemma tfsState_elim_net i n :
  tfsStateNet i n -> tfsStartStateNet i n \/
  (exists m, tfsNextStateNet m i n) \/
  tfsCurrStateNet i n \/ tfsBcStateNet i n \/
  tfsListenStateNet i n. intro. inversion H. inversion H0.
  inversion H2. inversion H4.
  left. netState_auto_tac.
  right. left. eexists. netState_auto_tac.
  right. right. left. netState_auto_tac.
  right. right. right. left. netState_auto_tac.
  right. right. right. right. netState_auto_tac.
  Qed.

Lemma tfsListen_failSafe_net m i n : reachableProtNet n ->
  tfsListenStateNet i n -> currModeNet m i n -> failSafe m.
(*Proof: Similar result for tfsBc, and one for tfsCurr but for the next mode
rather than the curr mode- perhaps inter-component results will be lifted
for these?*)
Proof.
  intros R TL CM. destruct TL as [e TLe E].
  lets CM' : liftEntNet_ent CM E. simpl in CM'. rewrite <- CM'.
  exact (proj2 (proj2 (tfs_failSafe_ent e (reachableNet_ent _ _ _ _ R E))) TLe).
Qed.

(*-LOCAL TIDY*)

Lemma tfs_currMode_disc_pres (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode) :
  reachableProtNet n -> n -NA- a -NA> n' -> currModeNet m i n -> ~ failSafe m ->
  tfsStateNet i n -> tfsStateNet i n'. intro RN. introz U.
  (*Destruct the tfs state into its components and apply an array of
  network level fwd-tracking results.*)
  apply tfsState_elim_net in U2. or_flat; ex_flat; [ |
  rename H into OR | ..];[eapply tfsStart_next_net in OR |
  eapply tfsNext_next_net in OR | eapply tfsCurr_next_net in OR |
  eapply tfsBc_next_net in OR | ];
  try eassumption; or_flat; ex_flat.
  (*Now we're left with a nubmber of cases where, in the hypotheses,
  you have that some tfs<..>StateNet holds. From here, we use lifting
  results previously defined*)
  apply tfsStart_tfs_net; assumption.
  eapply tfsNext_tfs_net; eassumption.
  eapply tfsNext_tfs_net; eassumption.
  apply tfsCurr_tfs_net; assumption.
  apply tfsCurr_tfs_net; assumption.
  apply tfsBc_tfs_net; assumption.
  apply tfsBc_tfs_net; assumption.
  apply tfsListen_tfs_net; assumption.
  (*The only case that differs is where we are tfsListen. In this case
  we observe that the currMode is failSafe.*)
  false. apply U1. eapply tfsListen_failSafe_net; eassumption.
  Qed. 

Lemma paused_switch_net (n : Network) (i : nat) :
  reachableProtNet n -> (pausedStateNet i n <-> switchStateNet i n). Admitted. (*4*)
(**Proof: Lift result from entity level ultimately- analogous theorems except with
reachableProt and prot level state predicates.*)

(** The broadcast timer counts down through a delay: a wait with a positive timer left came
from the wait with the timer longer by the delay. The broadcaster before the delay is a
broadcast state, as it is in a reachable network: sleeping, which is no wait; bcReady, which
is urgent; or a wait, whose timer was well formed and did not run out, since afterwards it
reads x > 0.*)
Lemma bcWaitNet_del_bkwd (n n' : Network) (m : Mode) (x : Time)
  (i : nat) (d : Delay) : broadcastStateNet i n -> zeroTime < x -> n -ND- d -ND> n' ->
  bcWaitStateNet m x i n' -> bcWaitStateNet m (x +dt+ d) i n.
Proof.
  intros BS XP D BW. net_state_destr BS p1 p2 p3 l h k E.
  net_state_destr BW p1' p2' p3' l' h' k' E'.
  lets S : link_net_ent_delW D E' E. lets T : triple_del_net D E E'. destruct T as [D1 _].
  net_state_intro E. red.
  destruct (broadcastState_shape _ BS) as [B | m' e B | m' l0 B].
  - (* sleeping delays to itself, and is no wait *)
    exfalso. apply (sleeping_not_bcWait m x).
    eapply bisim_trans; [ | exact BW]. apply bisim_symm.
    eapply bisim_del_pres; [del_self_body | exact B | exact D1].
  - destruct (bisim_step_del _ _ _ _ B D1) as [q [TQ BQ]].
    assert (BX : q ~p~ bcWait m x) by
      (eapply bisim_trans; [apply bisim_symm; exact BQ | exact BW]).
    clear BQ.
    destruct (bcWait_del_cases _ _ _ _ TQ) as [[t [H [EV EQ]]] | [[t [EV [LT [q' TP]]]] | [EV EQ]]];
      try subst q.
    + (* the timer counted down from t to x, so t = x + d *)
      destruct (bcWait_bisim_inj _ _ _ _ BX) as [EM ET]. subst m'.
      apply (f_equal (fun u => nonneg (time u))) in ET. simpl in ET.
      eapply bisim_trans; [exact B | ]. unfold bcWait.
      repeat apply choice_bisim_context; try apply bisim_refl.
      apply del_bisim_guard. rewrite EV. unfold liftTimeExp. rewrite evalExpFunTime_time.
      f_equal. apply timeEqR. simpl. lra.
    + (* the timer ran out during the delay: the derivative reads its position now, and a
         wait with x > 0 left cannot *)
      exfalso. destruct (bisim_disc_match _ _ _ _ BX TP) as [r R].
      apply bcWait_pos_read_inv in R. apply evalExpFunTime_zero_inv in R.
      simpl in XP. lra.
    + (* an ill-formed timer never runs out, but a wait with x left reads its position after x *)
      exfalso. destruct (bcWait_pos_read m x) as [[Z _] | [dx [qx [EQx [TDx [qx' Sx]]]]]].
      * simpl in XP. lra.
      * destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ BX) TDx) as [q1 [TD1 BQ1]].
        destruct (bisim_disc_match _ _ _ _ BQ1 Sx) as [r R].
        destruct (bcWait_del_cases _ _ _ _ TD1) as [[t [H [EV' _]]] | [[t [EV' _]] | [_ EQ1]]];
          try (rewrite EV in EV'; discriminate).
        subst q1. apply bcWait_pos_read_inv in R. rewrite EV in R. discriminate.
  - (* bcReady is urgent: the interface always takes its broadcast *)
    exfalso. eapply ent_del_sync_inter_not; [ | | exact S].
    + dae_broadcast. eapply bcReady_outProc_out_shape. exact B.
    + apply interface_outProc_in.
Qed.
(**Proof: Well, a backwards delay preservation would give us bcWaitState m x' i n for some x'. But forward tracking would then give us that
in the derivative state the second parameter is x' - d. So x = x' - d and so x' = x + d, as required.*)

(** Looks for an initial network in the hypotheses and also an entity in
that network and adds the hypothesis that the entity in question is initial.*)
Ltac initNet_ent_tac := let U0 := fresh in
  match goal with [U : initialProtNet ?n,
  U1 : ?e @ ?i .: ?n |- _] => lets U0 : initialNet_ent U U1 end.

(**Tactic for contradiction between initialProtNet and some state predicate.
Basically what it does is get the goal to the stage where there is a
hypothesis that says <...>State dormant/sleeping/listening, which is
immediately solvable by inversion because none of these initial processes
match the state predicate in quesion.*)
Ltac initNet_contra U :=
  let e := fresh "e" in let U1 := fresh U in let U2 := fresh U in
  destruct U as [e U1 U2]; initNet_ent_tac;
  match goal with [U4 : initialEnt _ e |- _] => inversion U4; subst e end;
  inversion U1; subst;
  match goal with [U6 : _ procProtocol |- _] => inversion U6 end; subst;
  match goal with
  | [U8 : context[dormant] |- _] => inversion U8
  | [U8 : context[sleeping] |- _] => inversion U8
  | [U8 : context[listening] |- _] => inversion U8
  end.


Lemma initial_not_bcWait_net (n : Network) (m : Mode) (x : Time) (i : nat) :
  initialProtNet n -> bcWaitStateNet m x i n -> False.
Proof.
  intros I B. destruct B as [e Be Ein].
  lets IE : initialNet_ent I Ein.
  destruct Be as [p l h k Bp]. inversion IE; subst.
  unfold procProtocol in Bp. inversion Bp; subst.
  eapply sleeping_not_bcWait; eassumption.
Qed.

(** If we're nextSince & we can delay, then we're in the ovWait state.*)
Lemma nextSince_del_ovWait (n n' : Network) (i : nat) (d : Delay) :
  reachableProtNet n -> n -ND- d -ND> n' -> nextSinceStateNet i n ->
  exists m t x y, ovWaitStateNet m t (delToTime (x +dt+ d)) (delToTime (y +dt+ d)) i n. Admitted. (*3*)
(**Proof: Apply nextSince_rel_state and then eliminate bcReady other urgent states. Also eliminate
the ovWaitStates whos time parameter is less than d (a weak sort of urgency)- have a weak urgency
result for this- it will depend on a timed out urgency. In general, the pattern is roughly that,
we prove P(0) is urgent, then show that P(d) can delay by at most d, this in turn rests on a proof
about delay prefixes, saying that e(d)P can only delay by d', where d is less than d', when P can
delay by d' - d.*)

(*This particular state combo means that the action must be tau & the interfaces of
the entity in question being preserved.*)
(* begin helpers for switchCurr_switchListen_net_link *)
(** No process is bisimilar to both switchCurr and switchListen.*)
Lemma switchCurr_switchListen_net_link_aux2 (p : ProcTerm) :
  switchCurrState p -> switchListenState p -> False.
Proof.
  intros S1 S2. lets D : switchCurr_mCurr_out S1.
  lets D2 : bisim_dae S2 D. inversion D2 as [q T].
  unfold switchListen in T. inversion T.
Qed.

(** If a triple whose overlap component is switchCurr performs a visible action that
switchCurr cannot perform, and the derivative's overlap component is switchListen,
then we have a contradiction.*)
Lemma switchCurr_switchListen_net_link_aux3 (p1 p2 p3 q1 q2 q3 : ProcTerm) (a : DiscAct) :
  switchCurrState p2 -> switchListenState q2 ->
  p1 $||$ p2 $||$ p3 -PA- a -PA> q1 $||$ q2 $||$ q3 -> a <> tauAct ->
  (forall q, switchCurr -PA- a -PA> q -> False) -> False.
Proof.
  intros S1 S2 T NT NSC. inversion T; subst; try (apply NT; reflexivity).
  - eapply switchCurr_switchListen_net_link_aux2; eassumption.
  - match goal with [H : p2 $||$ p3 -PA- a -PA> q2 $||$ q3 |- _] =>
      inversion H; subst; try (apply NT; reflexivity) end.
    + match goal with [H : p2 -PA- a -PA> q2 |- _] =>
        lets BM : bisim_disc_match S1 H end.
      destruct BM as [q BM]. eapply NSC. eassumption.
    + eapply switchCurr_switchListen_net_link_aux2; eassumption.
Qed.

(** A silent entity step from a switchCurr entity to a switchListen entity preserves
the interface.*)
Lemma switchCurr_switchListen_net_link_aux4 (p1 p2 p3 q1 q2 q3 : ProcTerm)
  (l l' : Position) (h h' : Interface) (k k' : ModeState) :
  switchCurrState p2 -> switchListenState q2 ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- aeTau ->> [|q1 $||$ q2 $||$ q3, l', h', k'|] ->
  h = h'.
Proof.
  intros S1 S2 T. inversion T; subst; try reflexivity; exfalso;
  (eapply switchCurr_switchListen_net_link_aux3;
    [ apply S1 | apply S2 | eassumption | discriminate
    | intros q TQ; unfold switchCurr in TQ; invert_disc_prefixes ]).
Qed.
(* end helpers *)

Lemma switchCurr_switchListen_net_link (n n' : Network) (i : nat)
  (a : ActDiscNet) (e e' : Entity) : 
  switchCurrStateEnt e -> switchListenStateEnt e' ->
  e @ i .: n -> e' @ i .: n' -> n -NA- a -NA> n' ->
  a = anTau /\ interEnt e = interEnt e'.
Proof.
  intros SC SL E E' STEP.
  destruct e as [p l h k]; destruct e' as [p' l' h' k'].
  inversion SC; subst.
  match goal with [H : switchCurrStateProt _ |- _] => inversion H; subst end.
  inversion SL; subst.
  match goal with [H : switchListenStateProt _ |- _] => inversion H; subst end.
  destruct a.
  (*Non-silent actions preserve the software component: contradiction.*)
  1-4: exfalso;
    lets PE : stepDiscNet_nonTau_pres_proc STEP E E';
    [ discriminate | ];
    simpl in PE; inversion PE; subst;
    eapply switchCurr_switchListen_net_link_aux2; eassumption.
  (*Silent action.*)
  split; [reflexivity | ].
  destruct (tauLink _ _ STEP) as [j [e0 [e0' [E0 [E0' [T R]]]]]].
  destruct (Nat.eq_dec j i) as [EQ | NEQ].
  - subst j.
    lets EA : entInNetUnique E0 E. lets EB : entInNetUnique E0' E'.
    subst e0 e0'. simpl. eapply switchCurr_switchListen_net_link_aux4; eassumption.
  - lets E1 : R NEQ E'.
    lets EQ : entInNetUnique E E1. inversion EQ; subst.
    exfalso. eapply switchCurr_switchListen_net_link_aux2; eassumption.
Qed.
(**Proof: Lift some EA::intercomponent & maybe some linking theorems
OR
Use some existing/new inversion tactics for destructing the state predicates and entities.*)

Lemma init_nextMode_net m i n :
  reachableProtNet n -> initStateNet m i n -> nextModeNet m i n.
  Admitted. (*7*)

(*LOCAL TIDY*)

Lemma nextMode_pres_fwd_net m i n n' a :
  reachableProtNet n -> nextModeNet m i n -> 
  ~(switchCurrStateNet i n \/ ovAbortStateNet i n \/
  (exists m0, tfsNextStateNet m0 i n) \/ tfsCurrStateNet i n) ->
  n -NA- a -NA> n' -> nextModeNet m i n'. Admitted. (*3*)
(**Proof: Brute force? Inter-component relationships? Is there any
machinery that you can use to help you prove this one?*)

Lemma ovWait_del_pres_bkwd_net_strong n n' d m t x y i : reachableProtNet n ->
  n -ND- d -ND> n' -> ovWaitStateNet m t x y i n' ->
  ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n. Admitted. (*#del-pres-net #strong*)

Lemma ovReady_del_pres_bkwd_net n n' d m t l i : overlapStateNet i n ->
  n -ND- d -ND> n' -> ovReadyStateNet m t l i n' ->
  ovReadyStateNet m t l i n.
Proof.
  intros OS D OR. apply (overlap_del_bkwd_net (ovReady m t l) _ _ _ _ OS D OR).
  intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
Qed.

(*-LOCAL TIDY*)

Lemma ovWait_ovReady_nextMode_net m t x y l i n :
  reachableProtNet n -> ovWaitStateNet m t x y i n \/ ovReadyStateNet m t l i n ->
  nextModeNet m i n.
  (*Proof: Induction on reachable using the auxialiary result init_nextMode_net.*)
  introz U. genDep5 m t x y l. induction U; intros l y x t m; introz V.
  (*
  (*Base case fails because neither ovWait nor ovReady is initial*)
  elim_intro V CON CON; initNet_contra CON.   
  Focus 2.  
  (*In the discrete inductive case, we show first that the previous state
  was either ovWait, ovReady, or init.*)
  assert ((exists t0 x0 y0, ovWaitStateNet m t0 x0 y0 i n) \/
  (exists t0 l0, ovReadyStateNet m t0 l0 i n) \/
  initStateNet m i n) as PREV.
  elim_intro V OVW OVR.
  lets OWP : ovWait_prev_net OVW s. elim_intro OWP OWL OWR.
  left. do 3 eexists. eassumption. right. or_flat; ex_flat.
  left. do 2 eexists. eassumption. right. eassumption.
  lets ORP : ovReady_prev_net OVR s. or_flat.
  right. left. do 2 eexists. eassumption.
  left. ex_flat. do 3 eexists. eassumption.
  (*Now we have that the previous state was either ovWait, ovReady or init,
  and so I.H. or the result init_nextMode_net will do*)
  clear V.
  (*First lets convert our goal to showing that the previous state had a next
  mode of m. We do this via a preservation tactic.*)
  cut (nextModeNet m i n). intro NM.
  (*The main thing to show here is that the previous state was not one
  that could have allowed a mode change.*)
  assert (~(switchCurrStateNet i n \/ ovAbortStateNet i n \/
  tfsCurrStateNet i n)) as NMC. unfold not. intro. or_flat; ex_flat;
  try rename H0 into H; try rename OR1 into OR; try rename OR2 into H;
  solve [state_pred_elim H OR; entnetuniq2 EN n; state_pred_elim H2 H0;
  subst; state_pred_elim H4 H6; state_pred_elim H5 H8].
  (*And from here we can show our (sub)goal.*)
  eapply nextMode_pres_fwd_net; eassumption.
  (*So now the proof burden that remains is to show the the next mode
  holds for the previous state.*)
  or_flat; ex_flat.
  (*In the ovWait and ovReady cases this follwos from the IH.*)
  lets IH : IHU l x2 x1 x0 m. apply IH. left. assumption.
  lets IH : IHU x1 y x x0 m. apply IH. right. assumption.
  (*Otherwise the auxialiary result init_nextMode_net works.*)
  eapply init_nextMode_net; eassumption.
  (*Now onto the delay case. For this we first use backward preservation of the state predicates
  to show that one holds in the previous case.*)
  assert (ovWaitStateNet m t x y i n \/ ovReadyStateNet m t l i n) as PREV.
  or_flat. left.
  (*Then we show by the inductive hypothesis that nextMode holds for 
  the previous case.*)
  (*Finally, forward preservation of the nextModeNet predicate by the
  delay relation gives us our goal.*)
  (*Going to have to fix this- apply new strong version of del_pres?*)
  eapply ovWait_del_pres_bkwd_net; eassumption.
  right. eapply ovReady_del_pres_bkwd_net; eassumption.
  eapply nextModeNet_del_pres; try eassumption.
  lets IH : IHU l y x t m. apply IH; assumption.
  Qed.*)
  Admitted. (*#bism-redo*)

Lemma ovWaitState_nextMode_net (n : Network) (m : Mode) (t x y : Time) (i : nat):
  reachableProtNet n -> ovWaitStateNet m t x y i n -> nextModeNet m i n.
  (*Proof: Use the more general result ovWait_ovReady_nextMode_net.*)
  introz U. eapply ovWait_ovReady_nextMode_net with (l := mkPosition 0 0).
  assumption. left. eassumption. Qed.

(*If a delay is possible, then every entity is in the listening state.*)
Theorem del_listening_net (n n' : Network) (d : Delay) (e : Entity) (i : nat) :
  reachableProtNet n -> n -ND- d -ND> n' -> e @ i .: n -> listeningStateNet i n.
  Admitted. (*7*)
(**Proof: Well if the network delays, then any member entity must also be able
to delay [del link theorem- salvaged?]. And then we can lift the result
(EA::del-listening-ent) to get that e is in the listening state, and we're done.*)



(********************************* Basic Results *********************************)

(*If v is incomingNetNotif with timestamp t, and the network can delay, then in
the derivative network v is incomingNetNotif with timestamp t - d.
Corollary is that whenever t = 0 delay is impossible.
This needs the notification to have the shape [r, m, l] of a range, a mode and a position,
since the listener can only input a notification of that shape.*)
Theorem incomingNetNotif_del (n n' : Network) (d : Delay) (r : Distance) (m : Mode)
  (lm : Position) (t : Time) (i : nat) :
  reachableProtNet n -> n -ND- d -ND> n' ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition lm] t i n ->
  {p : d <= t | incomingNetNotif [baseDistance r, baseMode m, basePosition lm]
    (minusTime t d p) i n'}.
  (*invert/destruct incomingNotif to [p, l, {li, lo, ln}, k] @ i.: n & v, t : ln*)
  intro RN. introz U. remember [baseDistance r, baseMode m, basePosition lm] as v eqn:Hv.
  destruct U0.
  (*Set up the derivaive entity.*)
  link_netentdelfwd_tac e' Y. destr_ent_inter e' p' l' k' li' lo' ln'.
  (*Apply ent-interface del linking tactic*)
  link_entinterdel_tac Y.
  (*Invert the delay to the lists.*)
  inversion_clear Y1.
  (*From here we split proof into two based on where d <= t or not*)
  Rleltcases d t IQ.
  (*In the case of d <= t we use a support lemma for the t - d stamp of the message*)
  exists IQ. econstructor. apply Y.
  eapply notifList_del_le. apply H3. assumption.
  (*In the case of t < d, proceed by contradiction on noSynchProcInter. We know that since
  a delay is possible for the entity, noSynch must be true between the entity components.*)
  false. assert (noSync p {| li := li; lo := lo; ln := ln |} k d) as NSY. inversion Y0.
  assumption. assert (p -PD- d -PD> p') as PDD. inversion Y0. assumption.
  (*So it suffices to falsify this to get the contradiction i.e. show a synch between proc
  and inter either now or after some delay less than d.*)
  lets NS : NSY (chanAN ;? v). decompAnd2 NS NSN NSD.
  (*Now we split into two subcases based on whether 0 < t or t = 0*)
  remember ([|p, l, {| li := li; lo := lo; ln := ln |}, k|]) as e0.
  timezerolteq t Q.
  (*If 0 < t then there is some delay d' = t*)
  clear NSN. mkdel t Q d'. assert (d' < d) as DD. rewrite Heqd'. assumption.
  (*Let's turn the inequality into an equation*)
  Rlttoplus DD x DP. mkdel x DP0 d''. assert (d = d' +d+ d'') as ED.
  rewrite Rplus_comm in DP. apply delayEqR. simpl. my_applys_eq DP.
  f_equal. rewrite Heqd''. reflexivity.
  (*Then by the property of time splitting, we get that there was an intermediate entity
  network from the original with delay d'. Call this n1.*)
  lets TNX : timeSplit_net U ED. decompExAnd TNX n1 ND1 ND2.
  (*Now, we know there must be some entity e1 in n1 which is delay linked to e0.*)
  link_netentdelfwd_tac e1 ED. 
  (*Now we do some inversion on this transiton to get the corresponding delay of the
  notification list.*)
  rewrite Heqe0 in ED1. destr_ent_inter e1 p1 l1 k1 li1 lo1 ln1.
  link_entinterdel_tac U. inversion U0. assert (d' <= t) as DT. rewrite Heqd'.
  simpl. apply Rle_refl.
  (*Once we have this delay, we can show that the notifList relation continues on,
  and since d' = t, the timestamp is now 0.*)
  lets ND : notifList_del_le DT H13 H0. assert (minusTime t d' DT = zeroTime) as TDZ.
  apply timeEqR. simpl. rewrite Heqd'. simpl. ring. rewrite TDZ in ND. clear TDZ.  
  (*Now we bring to our hypotheses the noSync condition for the intermediate state.*)
  assert (p -PD- d' -PD> p1 /\ k -ms- d' -ms> k1 /\
  {| li := li; lo := lo; ln := ln |} -i- d' -i> {| li := li1; lo := lo1; ln := ln1 |}).
  inversion ED1; (repeat split); assumption. andflat HY.
  lets NSF : NSD DD HY HY2 HY1.
  (*Then ahead we go to show the synchronisation on chanAN of v does exist.*)
  unfold noSyncNow in NSF. assert (discActEnabled p1 (chanAN;? v)) as DAE.
  rewrite Hv. apply listening_AN_prot. assert (listeningStateNet i n1) as LSN. eapply del_listening_net.
  eapply reachNetDel. apply RN. apply ND1. apply ND2. apply ED0. inversion LSN as [e IV1 IV2].
  inversion IV1 as [p4 l4 h4 k4 IV3 IV4]. my_applys_eq IV3. rewrite <- IV4 in IV2.
  entnetuniq2 EU n1. inversion EU. reflexivity. apply NSF in DAE. decompAnd2 DAE DI DM.
  apply DI. apply notif_timeout_enabled. assumption.
  (*If t = 0, then we have our contradiction with noSyncNow, just like the last step
  of the previous case.*)
  clear NSD. unfold noSyncNow in NSN. assert (discActEnabled p (chanAN;? v)) as DAE.
  rewrite Hv. apply listening_AN_prot. assert (listeningStateNet i n) as LSN. eapply del_listening_net.
  apply RN. apply U. apply H. inversion LSN. inversion H4. my_applys_eq H6.
  cut (e = e0). intros. rewrite H8 in H7. rewrite Heqe0 in H7. inversion H7.
  reflexivity. entnetuniq U e e0. assumption. apply NSN in DAE. decompAnd2 DAE DI DM.
  apply DI. assert (t = zeroTime) as TZ. apply timeEqR. rewrite <- Q.
  reflexivity. rewrite TZ in H0. apply notif_timeout_enabled. assumption. Qed.

(** Every entity of a reachable network is reachable.*)
Lemma reachable_net_ent : forall (n : Network) (e : Entity) (i : nat),
  reachableProtNet n -> e @ i .: n -> reachableProtEnt e.
Proof.
  intros n e i R E. exact (reachableNet_ent _ _ _ _ R E).
Qed.

Conjecture transGuard_disc_pres : forall (n n' : Network)
  (a : ActDiscNet) (t : Time) (i : nat),
  n -NA- a -NA> n' -> transGuard t i n -> transGuard t i n'.
(**Proof: Obvious: discrete action preserves guard on mode state, immediate from mode state semantics*)

Conjecture transGuard_del : forall (n n' : Network)
  (d : Delay) (t : Time) (i : nat),
  n -ND- d -ND> n' -> transGuard t i n -> 
  exists p, transGuard (minusTime t d p) i n'.
(**Proof: Obvious- transGuard definition and mode state semantics*)

(* begin helpers for currModeNet_dec *)
From Stdlib Require Import Classical.
(* end helpers *)

Lemma currModeNet_dec : forall (m : Mode) (i : nat) (n : Network),
  currModeNet m i n \/ ~currModeNet m i n.
Proof.
  intros m i n. apply classic.
Qed.
(**Proof: Obvious- not important to prove as it's just law of excluded middle*)

(**Delay preserves the current mode*)
Lemma currMode_del_pres_bkwd (n n' : Network) (d : Delay) (m : Mode) (i : nat) :
  n -ND- d -ND> n' -> currModeNet m i n' -> currModeNet m i n.
Proof.
  intros D C. apply (proj2 (currModeNet_del_pres n n' d m i D)). exact C.
Qed.
(**Proof: Follows directly from mode state semantics, and linking of delay from network to entity to modestate*)

Lemma nextMode_ent_ex : forall (m : Mode) (i : nat) (n : Network),
  nextModeNet m i n <-> exists e, e @ i .: n /\ nextModeEnt e = Some m.
Proof.
  intros m i n. split.
  - intros [e N E]. exists e. split; assumption.
  - intros [e [E N]]. econstructor; [exact N | exact E].
Qed.

Ltac currMode_ent_ex_tac e U :=
  let Q := fresh in let U1 := fresh U in let U2 := fresh U in
  match goal with
  [H : currModeNet ?m ?i ?n |- _ ] => lets Q : H; rewrite currMode_ent_ex in Q;
  decompExAnd Q e U1 U2
  end.

Ltac nextMode_ent_ex_tac e U :=
  let Q := fresh in let U1 := fresh U in let U2 := fresh U in
  match goal with
  [H : nextModeNet ?m ?i ?n |- _ ] => lets Q : H; rewrite nextMode_ent_ex in Q;
  decompExAnd Q e U1 U2
  end.

(*LOCAL TIDY*)

(** Given a network state predicate as the goal and the corresponding
entity state predicate in the hypotheses, this solves things using
lenWitness.*)
Ltac netState_ent_net_tac := eapply lenWitness;
  [eassumption | eassumption].

(** The network lift of tfsNext_currMode: the current mode and tfsNext's mode have the same
fail-safe successor.*)
Lemma tfsNext_currModeNet_eq m1 m2 i n : reachableProtNet n -> currModeNet m1 i n ->
  tfsNextStateNet m2 i n -> failSafeSucc m1 = failSafeSucc m2.
Proof.
  intros RN CM TN. apply currMode_ent_ex in CM. destruct CM as [e [EIN CE]].
  inversion TN as [e' TE EIN']. lets EQ : entInNetUnique EIN EIN'. subst e'.
  rewrite <- CE. apply (tfsNext_currMode e m2); [eapply reachable_net_ent; eassumption | exact TE].
Qed.

(** The nextSinceState relation can be broken down into the following cases.*)
Lemma nexSinceStateNet_cases i n :
  nextSinceStateNet i n ->
  (exists m t x y, ovWaitStateNet m t x y i n) \/
  (exists m t l, ovReadyStateNet m t l i n) \/
  (exists m, switchBcStateNet m i n) \/
  (switchCurrStateNet i n).
Proof.
  intros. inversion H. inversion H0. inversion H2. inversion H4.
  left. do 4 eexists. netState_auto_tac.
  right. left. do 3 eexists. netState_auto_tac.
  right. right. left. eexists. netState_auto_tac.
  right. right. right. netState_auto_tac.
Qed.

Ltac link_netentdisc_tac b :=
  match goal with
  | [ U1 : ?n -NA- ?a -NA> ?n', U2 : ?e @ ?i .: ?n,
  U3 : ?e' @ ?i .: ?n' |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_disc U1 U2 U3;
    let H2 := fresh in let H3 := fresh in
    elim_intro H1 H2 H3; [subst_all H2 |
    let H4 := fresh in invertClearAs2 H3 b H4]
  end.

(** Does some pre-processing on the proof of a backracking theorem at the
network level. Works where the backtracking has two predecessor cases.
Probably needs to be slightly altered if there's a need to handle more cases. *)
Ltac backtrack_net_pre U :=
  let U1 := fresh in let e := fresh "e" in let b := fresh "b" in
  state_pred_net_destr U; link_netentdiscbkwd_tac0 e b U1;
  let EQ := fresh "EQ" in let EX := fresh in
  match goal with [U2 : _ \/ _ |- _ ] =>
  elim_intro U2 EQ EX; [left; econstructor | ];
  [eassumption |  | ]; [ subst; assumption | ex_flat] end.

(** Tactic for eliminating two contradictory state predicates H and H1*)
Ltac state_pred_elim_net H H1 :=
  let e := fresh "e" in let e' := fresh "e'" in
  let U1 := fresh in let U2 := fresh in let U3 := fresh in
  let U1' := fresh in let U2' := fresh in
  inversion H as [e U1 U2]; inversion H1 as [e' U1' U2'];
  assert (e' = e) as U3;[eapply entInNetUnique; eassumption | ];
  subst_all U3; destruct e as [p0 l0 h0 k0]; inversion U1;
  inversion U1'; subst; 
  match goal with [SP1 : context[p0], SP2 : context[p0] |- _] =>
  inversion SP1; inversion SP2 end; subst;
  match goal with [PT : _ $||$ _ $||$ _ = ?p1 $||$ ?p2 $||$ ?p3 |- _] =>
  inversion PT; subst;
  repeat match goal with [PT : context[_ $||$ _ $||$ _] |- _] =>
  clear PT end;
  match goal with
  | [SP1 : context[p1], SP2 : context[p1] |- _] =>
    inversion SP1; subst; inversion SP2
  | [SP1 : context[p2], SP2 : context[p2] |- _] =>
    inversion SP1; subst; inversion SP2
  | [SP1 : context[p3], SP2 : context[p3] |- _] =>
    inversion SP1; subst; inversion SP2
  end
  end.

(***************************** Lifted results *****************************)

(** The overlap's backtracking lemmas, lifted. The process-level lemmas leave the earlier
ovWait's timers as expressions, which a reachable component may hold ill formed; these
conclude times, so they assume the timers well typed (ovWaitTypedNet). ovWait_prev_net
below needs no such hypothesis: the ovWait it starts from is typed already, and an ovReady
whose broadcast reaches a typed ovWait holds a time.*)
Lemma tfsStart_prev_net i n n' a : reachableProtNet n -> ovWaitTypedNet i n ->
  tfsStartStateNet i n' -> n -NA- a -NA> n' ->
  tfsStartStateNet i n \/ dormantStateNet i n \/
  exists m t x y, ovWaitStateNet m t x y i n.
  Admitted. (*#lift-track-net*)

Lemma ovReady_prev_net m t l i n n' a : reachableProtNet n -> ovWaitTypedNet i n ->
  ovReadyStateNet m t l i n' -> n -NA- a -NA> n' ->
  ovReadyStateNet m t l i n \/
  exists x y, ovWaitStateNet m t x y i n. Admitted. (*#lift-track-net*)

(*Organise these, write tactics for them, pull in results from elsewhere in
the file that belong here.*)

(** A delay keeps the overlap component waiting for the same mode and wait time; only its
timers change, as ovWait_del_pres says of the component.*)
Lemma ovWait_del_pres_net m t x y i n n' d : n -ND- d -ND> n' ->
  ovWaitStateNet m t x y i n -> exists x' y', ovWaitStateNet m t x' y' i n'.
Proof.
  intros D OW. net_state_destr OW p1 p2 p3 l h k E. lets T : triple_del_fwd_net D E.
  destruct T as [p1' [p2' [p3' [l' [h' [k' [E' [_ [D2 _]]]]]]]]].
  destruct (ovWait_del_pres _ _ _ _ _ _ _ OW D2) as [x' [y' OW']].
  exists x' y'. net_state_intro E'. exact OW'.
Qed.
(*Standard delay preservation tactic at network level, which itself
lifts from lower levels.*)

(** After a step into tfsNext, the overlap component was tfsStart or tfsNext already.*)
Lemma tfsNext_prev_net m i n n' a : overlapStateNet i n -> tfsNextStateNet m i n' ->
  n -NA- a -NA> n' -> tfsNextStateNet m i n \/ tfsStartStateNet i n.
Proof.
  intros OS TN S. net_state_destr OS p1 p2 p3 l h k E.
  net_state_destr TN p1' p2' p3' l' h' k' E'.
  lets T : triple_disc_net S E E'. destruct T as [_ [[EQ | [b B]] _]].
  - subst p2'. left. net_state_intro E. exact TN.
  - destruct (tfsNext_prev _ _ _ _ B OS TN) as [TS | TN2]; [right | left];
      net_state_intro E; assumption.
Qed.

Lemma del_pres_bkwd_tfsNext m i n n' d : overlapStateNet i n ->
  n -ND- d -ND> n' -> tfsNextStateNet m i n' -> tfsNextStateNet m i n.
Proof.
  intros OS D TN. apply (overlap_del_bkwd_net (tfsNext m) _ _ _ _ OS D TN).
  intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
Qed.
(*Proof: Lift delay preservation- write tactic for this*)

Lemma del_pres_bkwd_tfsStart i n n' d : overlapStateNet i n ->
  n -ND- d -ND> n' -> tfsStartStateNet i n' -> tfsStartStateNet i n.
Proof.
  intros OS D TS. apply (overlap_del_bkwd_net tfsStart _ _ _ _ OS D TS).
  intros m0 e2 e3 e4 B. ovWait_bisim_contra B.
Qed.

Lemma tfsNext_urgent_net m i n n' d : reachableProtNet n ->
  tfsNextStateNet m i n -> n -ND- d -ND> n' -> False.
Proof.
  intros RN U V. inversion U as [e SE EIN].
  destruct (del_net_ent e i n n' d EIN V) as [e' ED].
  inversion SE as [p l h k TP Hpe]. subst e.
  inversion TP as [p1 p2 p3 TS Hp]. subst p.
  assert (currModeNet (currModeEnt ([|p1 $||$ p2 $||$ p3, l, h, k|])) i n) as CM
    by (eapply currMode_intro; [reflexivity | exact EIN]).
  lets EQ : tfsNext_currModeNet_eq RN CM U. simpl in EQ.
  assert (currModeMState k -mtr-> failSafeSucc m) as FS
    by (rewrite <- EQ; apply failSafeSucc_successor).
  destruct (mState_stable_next_enabled _ _ FS) as [MS | MS].
  - eapply ent_del_sync_mState_not with (a := chanMStableWrite *!); [ | exact MS | exact ED].
    dae_overlap. eapply tfsNext_mStable_out. exact TS.
  - eapply ent_del_sync_mState_not with (a := chanMNextWrite ;! [baseMode (failSafeSucc m)]);
      [ | exact MS | exact ED].
    dae_overlap. apply tfsNext_mNext_out. exact TS.
Qed.

Lemma tfsStart_urgent_net i n n' d :
  tfsStartStateNet i n -> n -ND- d -ND> n' -> False.
Proof.
  intros U V. inversion U as [e SE EIN].
  destruct (del_net_ent e i n n' d EIN V) as [e' ED].
  inversion SE as [p l h k TP Hpe]. subst e.
  inversion TP as [p1 p2 p3 TS Hp]. subst p.
  eapply ent_del_sync_mState_not with (a := chanMCurrRead ;? [baseMode (currModeMState k)]);
    [ | apply modeState_curr_enabled | exact ED].
  dae_overlap. apply tfsStart_mCurr_in. exact TS.
Qed.

(** Across the broadcast from ovReady, the mode carries over and the position timer is set
to the period. ovWait's first parameter is only visible up to the period of the mode
(ovWait_params_bisim), so the earlier timer of ovReady and the new first parameter cannot
be tied to each other here.*)
Lemma ovReady_wait_track_net m t l i m' t' x y n n' a :
  ovReadyStateNet m t l i n -> ovWaitStateNet m' t' x y i n' ->
  n -NA- a -NA> n' -> m = m' /\ y = period m.
  Admitted. (*5*)
(*Proof: #lift-track-net*)

(** ovWait does not step to ovWait, so across a step its parameters are the same, the first
up to the period of the mode.*)
Lemma ovWait_track_net m m' t t' x x' y y' i n n' a :
  ovWaitStateNet m t x y i n -> ovWaitStateNet m' t' x' y' i n' ->
  n -NA- a -NA> n' ->
  m = m' /\ time t -nn- time (period m) = time t' -nn- time (period m) /\ x = x' /\ y = y'.
  Admitted. (*5*)
(**Proof: Apply a tactic to extract the underlying process state predicates- at the
lowest level e.g. ovWaitState p2 (tactic already exists I think?).
Then apply a matching tactic at this level, and you should be done.*)

(** After a step into ovWait, the entity was in ovWait already, in init, or in an ovReady
whose broadcast set the pause timer to its own timer less the period and the position
timer to the period.*)
Lemma ovWait_prev_net m t x y i n n' a : reachableProtNet n -> ovWaitStateNet m t x y i n' ->
  n -NA- a -NA> n' ->
  ovWaitStateNet m t x y i n \/
  (exists t0 l, ovReadyStateNet m t0 l i n /\
    time x = time t0 -nn- time (period m) /\ y = period m) \/
  initStateNet m i n.
  Admitted. (*#lift-track-net*)

Ltac reach_net_prot_tac :=
  match goal with [RN : reachableProtNet ?n,
  EIN : [|_, _, _, _|] @ _ .: ?n |- _] =>
  let RNP := fresh "RNP" in
  let RPT := fresh "RPT" in
  lets RNP : reachable_net_prot RN EIN;
  lets RPT : reachableProt_triple RNP end.

(*-LOCAL TIDY*)
