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
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.protocol.ProtAuxDefs.
From Stdlib Require Import Bool.
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtocolBridge.
From Stdlib Require Import Reals Lra.
From Stdlib Require Classical_Prop.

(****************** (TIDY?) General Stuff ******************)

Ltac invert_def := match goal with [ U : def _ = (_, _) |- _] =>
  invertClear U; subst end.

Ltac invert_trans := match goal with [P : _ -PA- _ -PA> _ |- _]
  => invertClear P; subst end.

Ltac clean_proc_trans := match goal with [U : _ -PA- _ -PA> _ |- _] =>
  clean_proc_hyp U end.

(** Given some application process in the context, this tactic performs inversion and
some cleanup on this until it is in the form of a process body as the source.*)
Ltac invert_app_trans := match goal with
  | [U : _ $( _ )$ -PA- _ -PA> _ |- _] => invertClear U; invert_def; clean_proc_trans
  | [U : liftNameProc _ -PA- _ -PA> _ |- _] => invertClear U; invert_def; clean_proc_trans
  end. 

(*Converts a hypothesis of an action for p1 or p2, into a hypothesis
of the same action by p1 + p2*)
Ltac lift_act_sum p1 p2 :=
  match goal with
  | [V : p1 -PA- ?a -PA> ?p' |- _] => apply (stepDpChoiceL p1 p2) in V
  | [V : p2 -PA- ?a -PA> ?p' |- _] => apply (stepDpChoiceR p1 p2) in V
  end.

(** A value of each type, for an input whose values are left open: a mode is taken from the
context, and the other types have closed inhabitants.*)
Ltac value_of_type t := lazymatch t with
  | vtMode => match goal with [m : Mode |- _] => constr:(baseMode m) end
  | vtTime => constr:(baseTime zeroTime)
  | vtPosition => constr:(basePosition origin)
  | vtDistance => constr:(baseDistance (mkDistance zeroNonneg))
  | vtDelay => constr:(baseDelay (mkDelay onePos))
  | vtNonneg => constr:(baseNonneg zeroNonneg)
  end.

(** A list of values typed for the variables xs: one value of each variable's type.*)
Ltac typed_witness xs := lazymatch xs with
  | nil => constr:(@nil BaseValue)
  | ?x :: ?xs' => let t := eval cbv in (varType x) in let v := value_of_type t in
    let vs := typed_witness xs' in constr:(v :: vs)
  end.

(*Converts a hypothesis of an action for p into one for b $> p, given that
evalBoolExp b true is a hypothesis.*)
Ltac lift_act_then b p := match goal with 
  [V1 : p -PA- ?a -PA> ?p', V2 : evalBoolExpFunTot b = true |- _] =>
  let V := fresh in rename V1 into V;
  lets V1 : stepDpThen V V2; clear V end.

(*Converts a hypothesis of an action on the body of n applied to x to a
hypothesis on the application process (n x)*)
Ltac lift_act_app h l2 :=
  match goal with
  | [V : unfoldApp h l2 -PA- _ -PA> _ |- _] => apply stepDpApp_alt in V
  end.

(*Generate all the discrete actions for some process p as hypotheses. Might leave some
boolean equalities over as contradictions to prove. Note: a posssilbe side-effect
of using this tactic is that any hypothesised actions on sub-terms of p will probably
be converted to actions on p. E.g. if we have H : p1 -a-> p' and then we do
gen_disc_acts (p1 + p2), we'll end up with H : p1 + p2 -a-> p'. Also this tactic hasn't
been written to work with parallel constructs, though this functionality could easily
be added.*)
Ltac gen_disc_acts p := 
  match p with
  | ?c $< ?l >$? ?p' => let V := fresh in let vs := typed_witness l in
    assert (p -PA- c ;? vs -PA>
    subProcTerm (listsToSub l (listBaselistExp vs)) p');
    [constructor; typed_vals | ]; remove_resets_hyp V; remove_updates_hyp V
  | ?c $< ?l >$! ?p' =>
    let EEL := fresh in let EELEQ := fresh in
    remember (evalExpListsFun l) as EEL eqn:EELEQ;
    destruct EEL; try solve [inversion EELEQ];
    match type of EELEQ with
    | Some ?l' = _ =>
      symmetry in EELEQ; assert (p -PA- c ;! l' -PA> p');
      [apply evalExpListsFunRel in EELEQ; econstructor;
      eassumption | ]; inversion EELEQ; subst
    | _ => idtac
    end; clear EELEQ
  | ?b $> ?p' =>
    let EEL := fresh in let EELEQ := fresh in
    remember (evalBoolExpFunTot b) as EEL eqn:EELEQ;
    destruct EEL; try solve [inversion EELEQ];
    match type of EELEQ with
    | true = _ => 
      symmetry in EELEQ; gen_disc_acts p'; lift_act_then b p'; clear EELEQ
    | _ => false
    end
  | ?p1 $+$ ?p2 => gen_disc_acts p1; gen_disc_acts p2; repeat lift_act_sum p1 p2
  | ?h $( ?l2 )$ => gen_disc_acts (unfoldApp h l2); repeat lift_act_app h l2
  | unfoldApp _ _ =>
    let p'' := fresh "p" in let Hp1 := fresh "Hp1" in 
    let Hp2 := fresh "Hp2" in
    remember p as p'' eqn:Hp1; lets Hp2 : Hp1; rewrite unfoldApp_body in Hp2; simpl in Hp2;
    remove_resets_hyp Hp2; remove_updates_hyp Hp2;
    match type of Hp2 with _ = ?q => gen_disc_acts q end;
    symmetry in Hp2; subst_all Hp2; subst_all Hp1
  | $< ?e >$ ?p' => idtac
  end.

(*A richer inversion on a transition that tries to get rid of definition hypotheses
and clean up some substitution stuff.*)
Ltac invert_trans_rich := invert_trans; try invert_def; clean_proc_trans.

(*Given a hypothesis V1 which says p ~ q, this tactic finds a hypotheses
of the form p -a> p', applies the bisimulation to yield the same for q, and then
tries to solve the goal by contradiction on this q-transition. If the contradiction
fails, then the tactic moves on to the next p-transition, and fails when there are
no more p-transitions left.*)
Ltac bisim_contra_rec V1 :=
  match type of V1 with ?p ~p~ ?q =>
  match goal with [V2 : p -PA- _ -PA> _ |- _] =>
  eapply bisim_disc_match in V2; [ | apply V1];
  let q' := fresh "q'" in let TR := fresh in
  invertClearAs2 V2 q' TR; first [
  solve [clear - TR; repeat invert_trans_rich]
  | bisim_contra_rec V1]
  end
  end.

(*Tried to solve by contradiction the assumption that two processes
are bisimilar, by generating the action of one, and trying to contradict
with the other. The parameter V1 that is passed in is a hypothesis of
bisimilarity between two process. Note that the contradiction generated
is only one-way.*)
Ltac bisim_contra V1 :=
  match type of V1 with ?p ~p~ ?q =>
  gen_disc_acts p; bisim_contra_rec V1
  end.

(*-TIDY?*)

(****************** Activation ******************)
(**Results about whether certain actions are enabled or not.
Activation results take a p and a predicate on p, and infer
that a certain action is available to p.*)

(*** Activation tactic stuff ***)

Ltac activation_pre_tac :=
  let U := fresh in 
  intro U; eapply bisim_dae; [apply bisim_symm; apply U | ];
  match goal with [ |- discActEnabled ?p ?a] =>
    match p with
    | ?p' => unfold p'
    | ?p' ?x1 => unfold p'
    | ?p' ?x1 ?x2 => unfold p'
    | ?p' ?x1 ?x2 ?x3 => unfold p'
    | ?p' ?x1 ?x2 ?x3 ?x4 => unfold p'
    | ?p' ?x1 ?x2 ?x3 ?x4 ?x5 => unfold p'
    end
  end.

Ltac activation_post_tac :=
  match goal with
  [ |- discActEnabled ?p ?a] => 
    match p with
    (*For sum, recursively go left and see if it succeeds, else go right.*)
    | _ $< _ >$ ? _  => apply dae_inPfx; typed_vals
    | _ $< _ >$ ! _  => apply dae_outPfx; constructor
    | ?p1 $+$ ?p2 => first [solve [apply daeSumL; activation_post_tac] |
      solve [apply daeSumR; activation_post_tac]]
    end
  end; repeat constructor.

Ltac activation_tac := activation_pre_tac; activation_post_tac.

(*** Results ***)

(** Unfolds the simple state predicates into bisimilarities. *)
Ltac prot_outProc_in_not_unfold :=
  unfold bcWaitState, sleepingState, bcReadyState, dormantState, ovWaitState,
    ovReadyState, switchBcState, switchCurrState, switchListenState,
    tfsStartState, tfsNextState, tfsCurrState, tfsBcState, tfsListenState,
    initState, ovAbortState, listeningState, rangeBadState, currOKState,
    abortOvlpState, badOvlpState, currCompState, pausedState, gotMsgState,
    gotRangeState, currEqState, nextEqState, currPincCheckState,
    nextPincCheckState in *.

(** Unfolds the bodies of the protocol component processes. *)
Ltac prot_outProc_in_not_body :=
  unfold bcWait, sleeping, bcReady, dormant, init, ovWait, ovReady, switchBc,
    switchCurr, switchListen, tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen,
    ovAbort, listening, checkRange, rangeBad, currEq, badOvlp, currOK, nextEq,
    abortOvlp, gotMsg, gotRange, currPincCheck, currComp, nextPincCheck,
    paused in *.

(** Anti-activation: given p ~p~ q and p -a-> p', transfer the transition to
    the concrete body q and refute it by brute-force inversion. *)
Ltac prot_outProc_in_not_contra :=
  prot_outProc_in_not_unfold;
  match goal with
  | [B : ?p ~p~ ?q, TR : ?p -PA- ?a -PA> ?p' |- _] =>
    let q' := fresh "q'" in let TR' := fresh "TR'" in
    destruct (bisim_disc_match _ _ _ _ B TR) as [q' TR'];
    prot_outProc_in_not_body; solve [invert_disc_prefixes]
  end.

(** Unfolds the applications and the bodies of the protocol's processes.*)
Ltac unfold_def_cbn := cbn [unfoldApp def protocolDefs protocolDef fst snd listsToSub
  liftVarList liftExpList subProcTerm subExp subBoolExp listSub map liftNameProc
  listBaselistExp bcWait sleeping bcReady dormant init ovWait ovReady switchBc switchCurr
  switchListen tfsStart tfsNext tfsCurr tfsBc tfsListen ovAbort listening checkRange
  rangeBad currEq badOvlp currOK nextEq abortOvlp gotMsg gotRange currPincCheck currComp
  nextPincCheck paused].

(** Rewrites a goal [app N args ~p~ T] into [body[args/vars] ~p~ T], with the substitution
computed away.*)
Ltac unfold_app_bisim := eapply bisim_trans; [apply app_bisim | ]; unfold_def_cbn; clean_proc.

(** Closes [p ~p~ X] from [B : p ~p~ q], where q is X, an application whose unfolding is X,
or nilProc.*)
Ltac shape_body B := solve [eapply bisim_trans; [exact B | ];
  first [apply bisim_refl | unfold_app_bisim; apply bisim_refl]].

(** From [H : p ~p~ X] and [T : p -PA- a -PA> p'], the matching step of X and its derivative
q with [B : p' ~p~ q]; then inverts the step on X's body, makes the input explicit and
computes the substitution in B.*)
Ltac shape_step_pre B :=
  match goal with [H : ?p ~p~ _, T : ?p -PA- _ -PA> _ |- _] =>
    let q := fresh "q" in let TQ := fresh "TQ" in
    destruct (bisim_step_disc _ _ _ _ H T) as [q [TQ B]]; clear H T end;
  prot_outProc_in_not_body; invert_disc_prefixes; explicit_typed_input; clean_proc_hyp B.

(** From [B : p ~p~ (b $> P) $+$ (!~ b $> Q)], in either order, the branch b selects:
[B : p ~p~ P], [p ~p~ Q], or [p ~p~ nilProc] when b is ill formed.*)
Ltac resolve_cond B :=
  let E := fresh "E" in let B2 := fresh B in
  match type of B with
  | _ ~p~ (!~ ?b $> ?Q) $+$ (?b $> ?P) =>
    lets B2 : bisim_trans B (choice_bisim_symm (!~ b $> Q) (b $> P)); clear B; rename B2 into B
  | _ => idtac end;
  match type of B with _ ~p~ (?b $> ?P) $+$ (!~ ?b $> ?Q) =>
    destruct (evalBoolExpFun b) as [ [ | ] | ] eqn:E;
    [ lets B2 : bisim_trans B (if_then_bisim_true b P Q (evalBoolExpFunRel _ _ E))
    | lets B2 : bisim_trans B (if_then_bisim_false b P Q (evalBoolExpFunRel _ _ E))
    | lets B2 : bisim_trans B (if_then_bisim_none b P Q E)];
    clear B E; rename B2 into B
  end.

(** Unfolds the application on the right of B, computing the substitution away.*)
Ltac unfold_app_hyp B :=
  let B2 := fresh B in
  pose proof (bisim_trans _ _ _ B (app_bisim _ _)) as B2; clear B; rename B2 into B;
  gen_app_intro unfold_def_cbn B; clean_proc_hyp B.

(** Solves [forall d q, X -PD- d -PD> q -> q = X] for a named state X without timers.*)
Ltac del_self_body := prot_outProc_in_not_body; del_self_tac.

(** Repeatedly inverts a delay of nilProc, a prefix, a sum or a delay guard.*)
Ltac invert_del_prefixes := repeat match goal with
  | [H : nilProc -PD- _ -PD> _ |- _] => inversion H; clear H; subst
  | [H : outPrefix _ _ _ -PD- _ -PD> _ |- _] => inversion H; clear H; subst
  | [H : inPrefix _ _ _ -PD- _ -PD> _ |- _] => inversion H; clear H; subst
  | [H : sum _ _ -PD- _ -PD> _ |- _] => inversion H; clear H; subst
  | [H : del _ _ -PD- _ -PD> _ |- _] => inversion H; clear H; subst
  end.

(** Closes [q ~p~ X e1 .. en] where q is X's body after a delay: each timer is the same, has
counted down, or has run out, in which case it is bisimilar to a zero timer.*)
Ltac del_timers_bisim := repeat apply choice_bisim_context;
  first [apply bisim_refl
    | apply bisim_symm; apply (del_zero_bisim (liftTimeExp zeroTime)); reflexivity].

(** Searches a sum of prefixes and zero timers for a step with the goal's action. An input
whose values are left open takes a value of each variable's type, a mode from the context.*)
Ltac step_search := first [ apply stepDpIn; typed_vals
  | match goal with [ |- inPrefix _ ?xs _ -PA- _ -PA> _ ] =>
      let vs := typed_witness xs in apply (stepDpIn _ vs xs); typed_vals end
  | solve [apply stepDpOut; repeat constructor]
  | apply stepDpTimeOut; [step_search | reflexivity]
  | apply stepDpChoiceL; step_search
  | apply stepDpChoiceR; step_search ].

(** A step of an application N(args) with the goal's action, found by unfolding it.*)
Ltac app_step := eapply stepDpApp; [reflexivity | ]; clean_proc; step_search.

(** Unfolds the application on the left of B, computing the substitution away.*)
Ltac unfold_app_hyp_l B :=
  let B2 := fresh B in
  pose proof (bisim_trans _ _ _ (bisim_symm _ _ (app_bisim _ _)) B) as B2; clear B;
  rename B2 into B; gen_app_intro unfold_def_cbn B; clean_proc_hyp B.

(** Refutes [BT : q ~p~ X], for bodies q and X with no application outside a prefix, by an
action one of them can do on a channel the other does not mention (step_chans). Each
channel is tried as a witness, in each direction.*)
Ltac chan_witness q c S :=
  first [ assert (S : exists v q', q -PA- c ;? v -PA> q') by (do 2 eexists; step_search)
        | assert (S : exists v q', q -PA- c ;! v -PA> q') by (do 2 eexists; step_search) ];
  let v := fresh "v" in let q' := fresh "q'" in destruct S as [v [q' S]].

(** Closes the goal from I : In cd l, computed to a disjunction of equalities, for a concrete
list l that does not hold cd.*)
Ltac chan_notin I := solve [decompose [or] I; first [discriminate | contradiction]].

Ltac refute_one q BT c :=
  let S := fresh "S" in let r := fresh "r" in let R := fresh "R" in let I := fresh "I" in
  chan_witness q c S;
  destruct (bisim_disc_match _ _ _ _ BT S) as [r R];
  pose proof (step_chans _ _ _ R) as I; specialize (I eq_refl); specialize (I _ eq_refl);
  simpl in I; chan_notin I.

Ltac refute_with_chans q BT cs :=
  lazymatch cs with
  | ?c :: ?cs' => first [ refute_one q BT c | refute_with_chans q BT cs' ]
  end.

Ltac refute_by_chan BT :=
  let cs := constr:(chanAN :: chanMStableRead :: chanMStableWrite :: chanMCurrRead
    :: chanMCurrWrite :: chanMNextRead :: chanMNextWrite :: chanPos
    :: chanOutProc :: chanInProc :: chanIOEnv :: chanTrans :: chanWake :: chanPause
    :: chanUnpause :: chanBad :: chanAbort :: nil) in
  match type of BT with ?q ~p~ ?X =>
    first [ refute_with_chans q BT cs
          | let BT' := fresh "BT" in pose proof (bisim_symm _ _ BT) as BT';
            refute_with_chans X BT' cs ] end.

(** Inverts the output lists of the steps found so far, so that the values output are the
values the prefixes hold.*)
Ltac output_values := repeat match goal with
  | [H : evalExpLists (liftExpList _) _ |- _] => unfold liftExpList in H
  | [H : evalExpLists (_ :: _) _ |- _] => inversion H; subst; clear H
  | [H : evalExpLists [] _ |- _] => inversion H; subst; clear H
  | [H : evalExp (eBase _) _ |- _] => inversion H; subst; clear H end.

(** Refutes [B : ovWait m e2 e3 e4 ~p~ Z] for a named overlap state Z other than ovWait, by
a channel one side uses and the other does not.*)
Ltac ovWait_bisim_contra B :=
  unfold ovWait, dormant, init, ovReady, switchBc, switchCurr, switchListen, ovAbort,
    tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen, liftNameProc in B; refute_by_chan B.

(** Writes every triple of components in H as an n-ary composition.*)
Ltac triple_parAll H :=
  repeat match type of H with context [?p1 $||$ ?p2 $||$ ?p3] =>
    change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]) in H end.

(** Turns a position in the three components into the named component: inverts the stepAt
and Forall2 facts an n-ary result gives on the three-element lists, computes the triple a
derived composition is, and closes the cases where two positions meant to differ coincide.*)
Ltac triple_pos :=
  positions_inv;
  repeat match goal with [E : _ = parAll _ _ |- _] =>
    cbn [parAll] in E; inversion E; subst; clear E end;
  try match goal with [N : ?x <> ?x |- _] => exfalso; exact (N eq_refl) end.

(** Inverts a step H of a triple on an action other than tau: exactly one component steps.*)
Ltac triple_disc_nonTau H :=
  triple_parAll H; apply parAll_disc_nonTau in H; [ | discriminate];
  destruct H as [? [? [? [? H]]]]; triple_pos.

(** From a discrete step H of a triple, each component is unchanged or steps.*)
Ltac triple_disc_weak H :=
  triple_parAll H; apply parAll_disc_weak in H;
  destruct H as [? [? [? H]]]; triple_pos.

(** Inverts a delay H of a triple into the delays of its components.*)
Ltac triple_del_inv H :=
  triple_parAll H; apply parAll_del_inv in H;
  destruct H as [? [? [? H]]]; triple_pos.

(** Asserts Q : the target of a step or delay H of a triple is a triple.*)
Ltac triple_shape H Q :=
  match type of H with
  | _ $||$ _ $||$ _ -PA- _ -PA> ?p' =>
    assert (Q : exists q1 q2 q3, p' = q1 $||$ q2 $||$ q3) by
      (triple_disc_weak H; do 3 eexists; reflexivity)
  | _ $||$ _ $||$ _ -PD- _ -PD> ?p' =>
    assert (Q : exists q1 q2 q3, p' = q1 $||$ q2 $||$ q3) by
      (triple_del_inv H; do 3 eexists; reflexivity)
  end.

(** From a discrete step H between triples, W : the first, second or third component is
unchanged or does some action.*)
Ltac link_partripdiscW_tac H W G :=
  assert (W : G); [triple_disc_weak H; assumption | ].

Section ProtAuxResults.
Context {Model : ComhModel}.

Lemma bcReady_outProc_out m l p :
  bcReadyState m l p -> discActEnabled p (chanOutProc ;! [baseMode m, basePosition l]).
  activation_tac. Qed.

Lemma tfsStart_mCurr_in (p : ProcTerm) (m : Mode) : tfsStartState p ->
  discActEnabled p (chanMCurrRead ;? [baseMode m]). activation_tac. Qed.

Lemma tfsNext_mStable_out (p : ProcTerm) (m : Mode) : tfsNextState m p ->
  discActEnabled p (chanMStableWrite *!). activation_tac. Qed.

Lemma tfsNext_mNext_out (p : ProcTerm) (m : Mode) : tfsNextState m p ->
  discActEnabled p (chanMNextWrite ;! ([baseMode (failSafeSucc m)])).
  activation_tac; apply daeSumL; apply dae_outPfx; constructor;
  constructor; try rewrite updateAppEq; assumption; constructor. Qed.

Lemma switchCurr_mCurr_out (p : ProcTerm) : switchCurrState p ->
  discActEnabled p (chanMCurrWrite *!). activation_tac. Qed.

Lemma switchListen_unpause_out (p : ProcTerm) : switchListenState p ->
  discActEnabled p (chanUnpause *!). activation_tac. Qed.

Lemma tfsCurr_bad_in (p : ProcTerm) : tfsCurrState p ->
  discActEnabled p (chanBad *?). activation_tac. Qed.

Lemma tfsCurr_abort_in (p : ProcTerm) : tfsCurrState p ->
  discActEnabled p (chanAbort *?). activation_tac. Qed.

Lemma tfsCurr_mCurr_out (p : ProcTerm) : tfsCurrState p ->
  discActEnabled p (chanMCurrWrite *!). activation_tac. Qed.

Lemma tfsListen_bad_in (p : ProcTerm) : tfsListenState p ->
  discActEnabled p (chanBad *?). activation_tac. Qed.

Lemma tfsListen_abort_in (p : ProcTerm) : tfsListenState p ->
  discActEnabled p (chanAbort *?). activation_tac. Qed.

Lemma tfsListen_unpause_out (p : ProcTerm) : tfsListenState p ->
  discActEnabled p (chanUnpause *!). activation_tac. Qed.

Lemma dormant_bad_in (p : ProcTerm) : dormantState p ->
  discActEnabled p (chanBad *?). activation_tac. Qed.

Lemma dormant_abort_in (p : ProcTerm) : dormantState p ->
  discActEnabled p (chanAbort *?). activation_tac. Qed.

Lemma dormant_mNext_in (p : ProcTerm) (m : Mode) : dormantState p ->
  discActEnabled p (chanMNextRead ;? [baseMode m]). activation_tac.
  Qed.

Lemma switchBc_wake_out m p : switchBcState m p ->
  discActEnabled p (chanWake ;! [baseMode m]). activation_tac. Qed.

Lemma sleeping_wake_in m p : sleepingState p ->
  discActEnabled p (chanWake ;? [baseMode m]). activation_tac. Qed.

Lemma bcWait_wake_in m m' x p : bcWaitState m' x p ->
  discActEnabled p (chanWake ;? [baseMode m]). activation_tac. Qed.

Lemma ovAbort_stable_out p : ovAbortState p -> discActEnabled p (chanMStableWrite *!).
  activation_tac. Qed.
 
Lemma tfsBc_trans_out p : tfsBcState p -> discActEnabled p (chanTrans *!).
  activation_tac. Qed.

Lemma bcWait_trans_in p m x : bcWaitState m x p -> discActEnabled p (chanTrans *?).
  activation_tac. Qed.

(** The same, for a broadcast component with any received values; see the component
shapes below.*)
Lemma bcWait_trans_in_shape (v : BaseValue) (e : Exp) p : p ~p~ bcWait v e ->
  discActEnabled p (chanTrans *?). activation_tac. Qed.

Lemma bcWait_wake_in_shape m (v : BaseValue) (e : Exp) p : p ~p~ bcWait v e ->
  discActEnabled p (chanWake ;? [baseMode m]). activation_tac. Qed.

Lemma bcReady_outProc_out_shape (v1 v2 : BaseValue) p : p ~p~ bcReady v1 v2 ->
  discActEnabled p (chanOutProc ;! [v1, v2]). activation_tac. Qed.

Lemma ovReady_outProc_out_shape (v1 : BaseValue) (e2 : Exp) (v3 : BaseValue) p :
  p ~p~ ovReady v1 e2 v3 -> discActEnabled p (chanOutProc ;! [v1, v3]).
  activation_tac. Qed.

Lemma sleep_trans_in p : sleepingState p -> discActEnabled p (chanTrans *?).
  activation_tac. Qed.

Lemma paused_unpause_in p : pausedState p -> discActEnabled p (chanUnpause *?).
  activation_tac. Qed.

(** The listener offers an unpause while listening.*)
Lemma listening_unpause_in p : listeningState p -> discActEnabled p (chanUnpause *?).
Proof. activation_tac. Qed.

(*** Versions of activation using sort ***)

Lemma paused_unpause_in_sort d p : pausedState p -> sort (chanUnpause *?) d p.
  intro Q. apply paused_unpause_in in Q. apply enabledInSort_in. assumption. Qed.
  
Lemma switchListen_unpause_out_sort d p : switchListenState p -> sort (chanUnpause *!) d p.
  intro Q. apply switchListen_unpause_out in Q. apply enabledInSort_out. assumption. Qed.

Lemma tfsListen_unpause_out_sort d p : tfsListenState p -> sort (chanUnpause *!) d p.
  intro Q. apply tfsListen_unpause_out in Q. apply enabledInSort_out. assumption. Qed.








(*** Non standard activation results - need a bit more thinking***)

(*Come up with an anti-activation tactic: inversion on the transition that was claimed
and show that none of the cases generated match any of the cases for the state predicate.*)
(**A listener process cannot output on the channel outProc.*)
(* begin helpers for listener_outProc_out_not *)

(* end helpers *)

(****************** Component shapes ******************)
(** broadcastState, overlapState and listenerState say that a component is reachable from
its initial process. Up to bisimilarity, such a component is in one of the named states.
The modes, positions and distances it holds are values of those types, because they arrived
by typed inputs; its timers and ranges are expressions, because they are computed. The
listener's conditional states resolve at once to the branch their condition selects. The
shapes do not record that a range evaluates to a number, so a condition on one may be ill
formed, and then the listener is stuck, which is to say bisimilar to nilProc. The lemmas
below prove these shapes, and the brute-force results about the components follow from them
by case analysis.*)

Inductive broadcastShape (p : ProcTerm) : Prop :=
  | shSleeping : p ~p~ sleeping -> broadcastShape p
  | shBcWait (m : Mode) (e : Exp) : p ~p~ bcWait m e -> broadcastShape p
  | shBcReady (m : Mode) (l : Position) : p ~p~ bcReady m l -> broadcastShape p.

Inductive overlapShape (p : ProcTerm) : Prop :=
  | shDormant : p ~p~ dormant -> overlapShape p
  | shInit (m : Mode) : p ~p~ init m -> overlapShape p
  | shOvWait (m : Mode) (e2 e3 e4 : Exp) : p ~p~ ovWait m e2 e3 e4 -> overlapShape p
  | shOvReady (m : Mode) (e2 : Exp) (l : Position) : p ~p~ ovReady m e2 l -> overlapShape p
  | shSwitchBc (m : Mode) : p ~p~ switchBc m -> overlapShape p
  | shSwitchCurr : p ~p~ switchCurr -> overlapShape p
  | shSwitchListen : p ~p~ switchListen -> overlapShape p
  | shOvAbort : p ~p~ ovAbort -> overlapShape p
  | shTfsStart : p ~p~ tfsStart -> overlapShape p
  | shTfsNext (m : Mode) : p ~p~ tfsNext m -> overlapShape p
  | shTfsCurr : p ~p~ tfsCurr -> overlapShape p
  | shTfsBc : p ~p~ tfsBc -> overlapShape p
  | shTfsListen : p ~p~ tfsListen -> overlapShape p.

Inductive listenerShape (p : ProcTerm) : Prop :=
  | shListening : p ~p~ listening -> listenerShape p
  | shRangeBad (m : Mode) : p ~p~ rangeBad m -> listenerShape p
  | shBadOvlp : p ~p~ badOvlp -> listenerShape p
  | shCurrOK (m : Mode) : p ~p~ currOK m -> listenerShape p
  | shAbortOvlp : p ~p~ abortOvlp -> listenerShape p
  | shGotMsg (m : Mode) (l : Position) : p ~p~ gotMsg m l -> listenerShape p
  | shGotRange (m : Mode) (e : Exp) : p ~p~ gotRange m e -> listenerShape p
  | shCurrComp (m : Mode) (e : Exp) : p ~p~ currComp m e -> listenerShape p
  | shPaused : p ~p~ paused -> listenerShape p
  | shStuck : p ~p~ nilProc -> listenerShape p.

(*** Tactics ***)

Ltac broadcast_shape_of B := first [
    eapply shSleeping; shape_body B | eapply shBcWait; shape_body B
  | eapply shBcReady; shape_body B ].

Ltac overlap_shape_of B := first [
    eapply shDormant; shape_body B | eapply shInit; shape_body B
  | eapply shOvWait; shape_body B | eapply shOvReady; shape_body B
  | eapply shSwitchBc; shape_body B | eapply shSwitchCurr; shape_body B
  | eapply shSwitchListen; shape_body B | eapply shOvAbort; shape_body B
  | eapply shTfsStart; shape_body B | eapply shTfsNext; shape_body B
  | eapply shTfsCurr; shape_body B | eapply shTfsBc; shape_body B
  | eapply shTfsListen; shape_body B ].

Ltac listener_shape_of B := first [
    eapply shStuck; exact B
  | eapply shListening; shape_body B | eapply shRangeBad; shape_body B
  | eapply shBadOvlp; shape_body B | eapply shCurrOK; shape_body B
  | eapply shAbortOvlp; shape_body B | eapply shGotMsg; shape_body B
  | eapply shGotRange; shape_body B | eapply shCurrComp; shape_body B
  | eapply shPaused; shape_body B
  | unfold_app_hyp B; resolve_cond B; listener_shape_of B ].

(*** The shapes are preserved ***)

Lemma bcWait_del_shape v e q d : bcWait v e -PD- d -PD> q -> exists e', q ~p~ bcWait v e'.
Proof.
  unfold bcWait. intro D. invert_del_prefixes; eexists; del_timers_bisim.
Qed.

Lemma ovWait_del_shape v e2 e3 e4 q d : ovWait v e2 e3 e4 -PD- d -PD> q ->
  exists e3' e4', q ~p~ ovWait v e2 e3' e4'.
Proof.
  unfold ovWait. intro D. invert_del_prefixes; do 2 eexists; del_timers_bisim.
Qed.

Lemma broadcastShape_disc p p' a : broadcastShape p -> p -PA- a -PA> p' -> broadcastShape p'.
Proof.
  intros S T. destruct S as [H | m e H | m l H]; shape_step_pre B; broadcast_shape_of B.
Qed.

Lemma broadcastShape_del p p' d : broadcastShape p -> p -PD- d -PD> p' -> broadcastShape p'.
Proof.
  intros S T. destruct S as [H | m e H | m l H].
  - apply shSleeping. eapply bisim_del_pres; [del_self_body | exact H | exact T].
  - destruct (bisim_step_del _ _ _ _ H T) as [q [TQ B]].
    destruct (bcWait_del_shape _ _ _ _ TQ) as [e' B'].
    eapply shBcWait. eapply bisim_trans; [exact B | exact B'].
  - eapply shBcReady. eapply bisim_del_pres; [del_self_body | exact H | exact T].
Qed.

Lemma overlapShape_disc p p' a : overlapShape p -> p -PA- a -PA> p' -> overlapShape p'.
Proof.
  intros S T.
  destruct S as [H | m H | m e2 e3 e4 H | m e2 l H | m H | H | H | H | H | m H | H | H | H];
    shape_step_pre B; overlap_shape_of B.
Qed.

Lemma overlapShape_del p p' d : overlapShape p -> p -PD- d -PD> p' -> overlapShape p'.
Proof.
  intros S T.
  destruct S as [H | m H | m e2 e3 e4 H | m e2 l H | m H | H | H | H | H | m H | H | H | H];
    [eapply shDormant | eapply shInit | idtac | eapply shOvReady | eapply shSwitchBc
    | eapply shSwitchCurr | eapply shSwitchListen | eapply shOvAbort | eapply shTfsStart
    | eapply shTfsNext | eapply shTfsCurr | eapply shTfsBc | eapply shTfsListen];
    try solve [eapply bisim_del_pres; [del_self_body | exact H | exact T]].
  destruct (bisim_step_del _ _ _ _ H T) as [q [TQ B]].
  destruct (ovWait_del_shape _ _ _ _ _ _ TQ) as [e3' [e4' B']].
  eapply shOvWait. eapply bisim_trans; [exact B | exact B'].
Qed.

Lemma listenerShape_disc p p' a : listenerShape p -> p -PA- a -PA> p' -> listenerShape p'.
Proof.
  intros S T. destruct S as [H | m H | H | m H | H | m l H | m e H | m e H | H | H];
    shape_step_pre B; listener_shape_of B.
Qed.

Lemma listenerShape_del p p' d : listenerShape p -> p -PD- d -PD> p' -> listenerShape p'.
Proof.
  intros S T. destruct S as [H | m H | H | m H | H | m l H | m e H | m e H | H | H];
    [eapply shListening | eapply shRangeBad | eapply shBadOvlp | eapply shCurrOK
    | eapply shAbortOvlp | eapply shGotMsg | eapply shGotRange | eapply shCurrComp
    | eapply shPaused | eapply shStuck];
    (eapply bisim_del_pres; [del_self_body | exact H | exact T]).
Qed.

(*** The shape lemmas ***)

Lemma broadcastState_shape p : broadcastState p -> broadcastShape p.
Proof.
  apply reachableFrom_invariant; [apply shSleeping, bisim_refl | | ].
  - intros q q' a. apply broadcastShape_disc.
  - intros q q' d. apply broadcastShape_del.
Qed.

Lemma overlapState_shape p : overlapState p -> overlapShape p.
Proof.
  apply reachableFrom_invariant; [apply shDormant, bisim_refl | | ].
  - intros q q' a. apply overlapShape_disc.
  - intros q q' d. apply overlapShape_del.
Qed.

Lemma listenerState_shape p : listenerState p -> listenerShape p.
Proof.
  apply reachableFrom_invariant; [apply shListening, bisim_refl | | ].
  - intros q q' a. apply listenerShape_disc.
  - intros q q' d. apply listenerShape_del.
Qed.

(** The listener's conditions evaluate when their values do: a sufficiency test on a mode and a
distance, an equality test, and a threat test whose range evaluates to a number.*)
Local Lemma suff_eval_some (m : Mode) (r : Distance) :
  evalBoolExpFun (bSufficient (eBase (baseMode m)) (eBase (baseDistance r))) <> None.
Proof. destruct r as [r]. simpl. discriminate. Qed.

Local Lemma equal_eval_some (b1 b2 : BaseValue) :
  evalBoolExpFun (bEqual (eBase b1) (eBase b2)) <> None.
Proof. simpl. destruct (eqDecBase b1 b2); discriminate. Qed.

Local Lemma possInc_eval_some (m1 m2 : Mode) (e : Exp) (b : BaseValue) (r : nonnegreal) :
  evalExpFun e = Some b -> evalBaseNonnegFun b = Some r ->
  evalBoolExpFun (bPossInc (eBase (baseMode m1)) (eBase (baseMode m2)) e) <> None.
Proof. intros Ee Eb. simpl. rewrite Ee, Eb. discriminate. Qed.

(** The range gotMsg computes from two positions evaluates to a number.*)
Local Lemma msg_range_eval (l l' : Position) : exists b r,
  evalExpFun ((| eBase (basePosition l), eBase (basePosition l') |) (-) speedMax (.) msgLatency)
    = Some b /\ evalBaseNonnegFun b = Some r.
Proof.
  simpl. destruct msgLatency as [ml]. simpl. do 2 eexists. split; reflexivity.
Qed.

(** From [B : p ~p~ (b $> P) $+$ (!~ b $> Q)], in either order, the branch b selects, for b
one of the listener's conditions, which evaluate.*)
Local Ltac resolve_cond_ranged B :=
  let E := fresh "E" in let B2 := fresh B in
  match type of B with
  | _ ~p~ (!~ ?b $> ?Q) $+$ (?b $> ?P) =>
    lets B2 : bisim_trans B (choice_bisim_symm (!~ b $> Q) (b $> P)); clear B; rename B2 into B
  | _ => idtac end;
  match type of B with _ ~p~ (?b $> ?P) $+$ (!~ ?b $> ?Q) =>
    destruct (evalBoolExpFun b) as [ [ | ] | ] eqn:E;
    [ lets B2 : bisim_trans B (if_then_bisim_true b P Q (evalBoolExpFunRel _ _ E));
      clear B E; rename B2 into B
    | lets B2 : bisim_trans B (if_then_bisim_false b P Q (evalBoolExpFunRel _ _ E));
      clear B E; rename B2 into B
    | exfalso; first [ exact (suff_eval_some _ _ E) | exact (equal_eval_some _ _ E)
                     | eapply possInc_eval_some; [eassumption | eassumption | exact E] ] ]
  end.

(** Closes [q ~p~ X] from [B : q ~p~ Y], where Y is X or an application that unfolds to X.*)
Local Ltac ranged_body B := solve [eapply bisim_trans; [exact B | ];
  first [apply bisim_refl | unfold_app_bisim; apply bisim_refl]].

(** Closes the refined listener shape of q from B : q ~p~ X, for X a derivative of a listener
state.*)
Local Ltac ranged_of B := first [
    left; ranged_body B
  | right; left; eexists; ranged_body B
  | right; right; left; ranged_body B
  | right; right; right; left; eexists; ranged_body B
  | right; right; right; right; left; ranged_body B
  | right; right; right; right; right; left; do 2 eexists; ranged_body B
  | right; right; right; right; right; right; left;
    match type of B with _ ~p~ _ $( [_, ?e] )$ =>
      first [ match e with
              | eSubtract (eDist (eBase (basePosition ?l0)) (eBase (basePosition ?l1))) _ =>
                destruct (msg_range_eval l0 l1) as [rb [rr [Ee Eb]]];
                eexists; exists e rb rr; split; [ranged_body B | split; [exact Ee | exact Eb]] end
            | do 4 eexists; split; [ranged_body B | split; eassumption] ] end
  | right; right; right; right; right; right; right; left;
    do 4 eexists; split; [ranged_body B | split; eassumption]
  | right; right; right; right; right; right; right; right; ranged_body B
  | unfold_app_hyp B; resolve_cond_ranged B; ranged_of B ].

(** Up to bisimilarity, a listener state is one of the named states, and the ranges gotRange and
currComp hold evaluate to numbers. So, unlike listenerShape allows, it is never stuck.*)
Lemma listenerState_shape_ranged p : listenerState p ->
  p ~p~ listening \/ (exists (m : Mode), p ~p~ rangeBad m) \/ p ~p~ badOvlp \/
  (exists (m : Mode), p ~p~ currOK m) \/ p ~p~ abortOvlp \/
  (exists (m : Mode) (l : Position), p ~p~ gotMsg m l) \/
  (exists (m : Mode) (e : Exp) (b : BaseValue) (r : nonnegreal),
     p ~p~ gotRange m e /\ evalExpFun e = Some b /\ evalBaseNonnegFun b = Some r) \/
  (exists (m : Mode) (e : Exp) (b : BaseValue) (r : nonnegreal),
     p ~p~ currComp m e /\ evalExpFun e = Some b /\ evalBaseNonnegFun b = Some r) \/
  p ~p~ paused.
Proof.
  intro LS. pattern p. apply (reachableFrom_invariant _ listening);
    [left; apply bisim_refl | | | exact LS].
  - intros q q' a J T.
    destruct J as [H | [[m H] | [H | [[m H] | [H | [[m [l H]] |
      [[m [e [b [r [H [Ee Eb]]]]]] | [[m [e [b [r [H [Ee Eb]]]]]] | H]]]]]]]];
      shape_step_pre B;
      try (match goal with [Ee : evalExpFun ?e = Some _ |- _] =>
             rewrite (eval_pres_sub _ _ _ (evalExpFunRel _ _ Ee)) in B end);
      ranged_of B.
  - intros q q' d J D.
    destruct J as [H | [[m H] | [H | [[m H] | [H | [[m [l H]] |
      [[m [e [b [r [H [Ee Eb]]]]]] | [[m [e [b [r [H [Ee Eb]]]]]] | H]]]]]]]].
    + left. eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + right; left. exists m. eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + right; right; left. eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + do 3 right; left. exists m. eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + do 4 right; left. eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + do 5 right; left. exists m l. eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + do 6 right; left. exists m e b r. split; [ | split; assumption].
      eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + do 7 right; left. exists m e b r. split; [ | split; assumption].
      eapply bisim_del_pres; [del_self_body | exact H | exact D].
    + do 8 right. eapply bisim_del_pres; [del_self_body | exact H | exact D].
Qed.

Theorem listener_outProc_out_not (p p' : ProcTerm) (v : list BaseValue) : 
  listenerState p -> p -PA- chanOutProc ;! v -PA> p' -> False.
Proof.
  intros LS TR. destruct (listenerState_shape _ LS); prot_outProc_in_not_contra.
Qed.
(**Proof sketch: Because none of its constituents can output on said channel.*)

(** A process in the listening state is listening on the channel AN, for any
notification [r, m'', l'] of a range, a mode and a position.*)
Lemma listening_AN_prot p (r : Distance) (m : Mode) (l : Position) :
  listeningStateProt p ->
  discActEnabled p (chanAN ;? [baseDistance r, baseMode m, basePosition l]).
Proof.
  intros LS. inversion LS as [p1 p2 p3 Q]; subst.
  apply daeParR; apply daeParR.
  eapply bisim_dae; [apply bisim_symm; apply Q | ]. unfold listening.
  apply daeSumL; apply daeSumL; apply daeSumL. apply dae_inPfx. typed_vals.
Qed.
(**Proof: Lift an activation result from simple level.
Come up with a general tactic for that lifting?*)


(****************** Tracking ******************)
(**Results which take a transition across processes and derive information on this
transition based on the nature of the source/derivative process. Fwd tracking takes
p -PA- a -PA> p' and a predicate on p & infers something about a & p' (usuall the channel
& tuple type of a and a simple state predicate on p'). Back tracking is similar,
but works the opposite direction: starting with a predicate on p' and inferring a
and p from there.*)

(*** Bidirectional tracking (action/variable matching) ***)

Lemma abortOvlp_listening_track (p p' : ProcTerm) (a : DiscAct) :
  abortOvlpState p -> listeningState p' -> p -PA- a -PA> p' ->
  a = chanAbort;! [].
Proof.
  intros CS LS TR. unfold abortOvlpState, abortOvlp in CS.
  destruct (bisim_disc_match _ _ _ _ CS TR) as [q TQ]. invert_disc_prefixes.
  match goal with [H : evalExpLists [] _ |- _] => inversion H end.
  reflexivity.
Qed.

(*** Results ***)

(*Assuming we've already been through m existentials, this tactic works
by matching P with a function applied to some number of arguments and then
converts the required amount of arguments to existentials.*)

(*** Back tracking ***)

End ProtAuxResults.

(** Pre-processing for a back-tracking result, with [TR : p -PA- a -PA> p'],
[O : overlapState p] and [SP : p' ~p~ X] in the context. For each shape of p, the matching
step of its body into q, with [BT : q ~p~ X], the input made explicit and the substitution
computed; then the shapes whose derivative is not bisimilar to X are refuted.*)
Ltac backtrack_shape SP :=
  match goal with [TR : ?p -PA- _ -PA> _, O : overlapState ?p |- _] =>
    destruct (overlapState_shape _ O)
      as [B | ?m B | ?m ?e2 ?e3 ?e4 B | ?m ?e2 ?l B | ?m B | B | B | B | B | ?m B | B | B | B];
    let q := fresh "q" in let TQ := fresh "TQ" in let BQ := fresh "BQ" in
    let BT := fresh "BT" in
    destruct (bisim_step_disc _ _ _ _ B TR) as [q [TQ BQ]];
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ BQ) SP) as BT;
    prot_outProc_in_not_body; invert_disc_prefixes; explicit_typed_input; clean_proc_hyp BT;
    unfold liftNameProc in BT; try unfold_app_hyp_l BT; prot_outProc_in_not_body;
    try solve [refute_by_chan BT]
  end.

Section ProtAuxResults.
Context {Model : ComhModel}.

(** Asserts S : q -PA- act -PA> q' for the source q of BT, a body or an application, and the
derivative q' the search finds.*)
Ltac bt_step BT act S := match type of BT with ?q ~p~ _ =>
  eassert (S : q -PA- act -PA> _) by first [step_search | app_step] end.

(** After a step into tfsStart, the overlap component was dormant or waiting: both take a
bad message there.*)
Lemma tfsStart_prev (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> overlapState p -> tfsStartState p' ->
  dormantState p \/ exists (m : Mode) e2 e3 e4, p ~p~ ovWait m e2 e3 e4.
Proof.
  intros TR O SP. red in SP. backtrack_shape SP;
    first [left; exact B | right; do 4 eexists; exact B].
Qed.

(** After a step into tfsNext, the overlap component was tfsStart, or was tfsNext already:
tfsNext loops when it writes on mStable.*)
Theorem tfsNext_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) :
  p -PA- a -PA> p' -> overlapState p -> tfsNextState m p' ->
  tfsStartState p \/ tfsNextState m p.
Proof.
  intros TR O SP. red in SP. backtrack_shape SP.
  - left. exact B.
  - right. red. eapply bisim_trans; [exact B | ]. eapply bisim_trans; [ | exact BT].
    apply bisim_refl.
Qed.

(** After a step into tfsCurr, the overlap component was tfsNext, or tfsCurr already.*)
Lemma tfsCurr_prev (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> overlapState p -> tfsCurrState p' ->
  tfsCurrState p \/ exists m, tfsNextState m p.
Proof.
  intros TR O SP. red in SP. backtrack_shape SP;
    first [left; exact B | right; eexists; exact B].
Qed.

(** After a step into tfsBc, the overlap component was tfsCurr.*)
Lemma tfsBc_prev (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> overlapState p -> tfsBcState p' -> tfsCurrState p.
Proof.
  intros TR O SP. red in SP. backtrack_shape SP; exact B.
Qed.

(** After a step into tfsListen, the overlap component was tfsBc, or tfsListen already.*)
Lemma tfsListen_prev (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> overlapState p -> tfsListenState p' ->
  tfsListenState p \/ tfsBcState p.
Proof.
  intros TR O SP. red in SP. backtrack_shape SP; first [left; exact B | right; exact B].
Qed.

(** tfsNext shows its mode only through the fail-safe successor it writes on mNext, so two
bisimilar tfsNext agree on that successor and need not agree on the mode.*)
Lemma tfsNext_bisim_param (v m : Mode) :
  tfsNext v ~p~ tfsNext m -> failSafeSucc v = failSafeSucc m.
Proof.
  intro B.
  eassert (S : tfsNext v -PA- chanMNextWrite ;! [baseMode (failSafeSucc v)] -PA> _)
    by (unfold tfsNext; step_search).
  destruct (bisim_disc_match _ _ _ _ B S) as [q R]. unfold tfsNext in R.
  invert_disc_prefixes.
  repeat match goal with
    | [H : evalExpLists _ _ |- _] => inversion H; subst; clear H
    | [H : evalExp (eFailSafeSucc _) _ |- _] => inversion H; subst; clear H
    | [H : evalExp (eBase _) _ |- _] => inversion H; subst; clear H end.
  congruence.
Qed.

(** After a step into ovWait, the overlap component was init, or was ovReady and the step
was its broadcast. The mode and position of that ovReady are whatever values it held: tying
them to m and to the output takes a timing argument, since ovWait's parameters are only
observable through its timers.*)
Theorem ovWait_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) (t x y : Time) :
  p -PA- a -PA> p' -> overlapState p -> ovWaitState m t x y p' ->
  initState m p \/ exists (v l : BaseValue) (u : Exp),
  p ~p~ ovReady v u l /\ a = chanOutProc ;! [v, l].
Proof.
  intros TR O SP. red in SP. backtrack_shape SP.
  - (* init: its derivative can read its position at once, so ovWait m t x y can too, and
       both derivatives then broadcast their modes, which therefore agree.*)
    bt_step BT (chanPos ;? [basePosition origin]) S1.
    destruct (bisim_step_disc _ _ _ _ BT S1) as [r1 [R1 BR1]].
    invert_disc_prefixes. clean_proc_hyp BR1.
    match type of BR1 with app _ (eBase ?b :: _) ~p~ _ =>
      bt_step BR1 (chanOutProc ;! [b, basePosition origin]) S2 end.
    destruct (bisim_step_disc _ _ _ _ BR1 S2) as [r2 [R2 _]].
    invert_app_trans. invert_disc_prefixes. output_values.
    left. exact B.
  - right. output_values. do 3 eexists. split; [exact B | reflexivity].
Qed.

(** The step into ovReady reads the position ovReady holds: its derivative broadcasts that
position, so the value read is the one ovReady m t l holds, whatever its timer.*)
Theorem ovReady_prev_act (p p' : ProcTerm) (a : DiscAct) (m : Mode) (t : Exp) (l : Position) :
  p -PA- a -PA> p' -> overlapState p -> ovReadyStateExp m t l p' ->
  a = chanPos ;? [basePosition l].
Proof.
  intros TR O SP. red in SP. backtrack_shape SP.
  match type of BT with outPrefix _ (eBase ?b1 :: eBase ?b :: nil) _ ~p~ _ =>
    bt_step BT (chanOutProc ;! [b1, b]) S2 end.
  destruct (bisim_step_disc _ _ _ _ BT S2) as [r2 [R2 _]].
  invert_disc_prefixes. output_values. reflexivity.
Qed.

(** The step into bcReady reads the position bcReady holds, as for ovReady: the broadcast
component was bcWait with its timer run out, and no other broadcast state reaches bcReady.*)
Theorem bcReady_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) (l : Position) :
  p -PA- a -PA> p' -> broadcastState p -> bcReadyState m l p' ->
  a = chanPos ;? [basePosition l].
Proof.
  intros TR O SP. red in SP.
  destruct (broadcastState_shape _ O) as [B | m0 e B | m0 l0 B];
  (let q := fresh "q" in let TQ := fresh "TQ" in let BQ := fresh "BQ" in let BT := fresh "BT" in
    destruct (bisim_step_disc _ _ _ _ B TR) as [q [TQ BQ]];
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ BQ) SP) as BT;
    prot_outProc_in_not_body; invert_disc_prefixes; explicit_typed_input; clean_proc_hyp BT;
    unfold liftNameProc in BT; try unfold_app_hyp_l BT; prot_outProc_in_not_body;
    try solve [refute_by_chan BT]).
  match type of BT with outPrefix _ (eBase ?b1 :: eBase ?b :: nil) _ ~p~ _ =>
    bt_step BT (chanOutProc ;! [b1, b]) S2 end.
  destruct (bisim_step_disc _ _ _ _ BT S2) as [r2 [R2 _]].
  invert_disc_prefixes. output_values. reflexivity.
Qed.

(** After a step into switchBc, the overlap component was ovWait with its pause timer run
out.*)
Theorem switchBc_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) :
  p -PA- a -PA> p' -> overlapState p -> switchBcState m p' ->
  exists t y, ovWaitStateExp m t zeroTime y p.
Proof.
  intros TR O SP. red in SP. backtrack_shape SP.
  (* ovWait: its derivative wakes the broadcaster with its mode, so switchBc m matches that
     output, which fixes the mode.*)
  match type of BT with outPrefix _ (eBase ?b :: nil) _ ~p~ _ =>
    bt_step BT (chanWake ;! [b]) S2 end.
  destruct (bisim_step_disc _ _ _ _ BT S2) as [r2 [R2 _]].
  invert_disc_prefixes. output_values.
  exists e2 e4. red. eapply bisim_trans; [exact B | ]. unfold ovWait.
  repeat apply choice_bisim_context;
    first [apply bisim_refl
      | apply del_bisim_guard;
        match goal with [E : evalExpFunTime _ = Some zeroTime |- _] => rewrite E end;
        reflexivity].
Qed.

(*** ovWait's parameters under bisimilarity ***)
(** ovWait shows its parameters only through its timers: x and y directly, the mode m through
the pause and the broadcast, and t only through the timers it sets after the broadcast,
which subtract the period of the mode from it. So two ovWait whose parameters evaluate to
the same times, the first up to the period, are bisimilar. The relation below pairs them,
with the ovReady they broadcast from and with pairs already bisimilar, and its steps
match.*)

Inductive ovWaitRel (m : Mode) : ProcTerm -> ProcTerm -> Prop :=
  | owrWait (p q : ProcTerm) (u u' x x' y y' : Exp) (tu tu' tx ty : Time) :
      p ~p~ ovWait m u x y -> q ~p~ ovWait m u' x' y' ->
      evalExpFunTime u = Some tu -> evalExpFunTime u' = Some tu' ->
      time tu -nn- time (period m) = time tu' -nn- time (period m) ->
      evalExpFunTime x = Some tx -> evalExpFunTime x' = Some tx ->
      evalExpFunTime y = Some ty -> evalExpFunTime y' = Some ty ->
      ovWaitRel m p q
  | owrReady (p q : ProcTerm) (u u' : Exp) (l : Position) (tu tu' : Time) :
      p ~p~ ovReady m u l -> q ~p~ ovReady m u' l ->
      evalExpFunTime u = Some tu -> evalExpFunTime u' = Some tu' ->
      time tu -nn- time (period m) = time tu' -nn- time (period m) ->
      ovWaitRel m p q
  | owrBisim (p q : ProcTerm) : p ~p~ q -> ovWaitRel m p q.

Lemma ovWaitRel_sym m p q : ovWaitRel m p q -> ovWaitRel m q p.
Proof.
  intro R. destruct R.
  - eapply owrWait; try eassumption. symmetry. assumption.
  - eapply owrReady; try eassumption. symmetry. assumption.
  - apply owrBisim. apply bisim_symm. assumption.
Qed.



(** The derivative of ovWait's body after a delay, or an application's unfolding, is an
ovWait with the timers that are left, with zero for a timer that has run out.*)
Ltac ovWait_timers_bisim := unfold ovWait; repeat apply choice_bisim_context;
  first [apply bisim_refl
    | apply bisim_symm; apply (del_zero_bisim (liftTimeExp zeroTime)); reflexivity].

(** Closes ovWaitRel for the derivatives of a delay: both are ovWait up to the timers
left, whose values are those literal times.*)
Ltac close_wait Br Bq' Eu Eu' Emod :=
  eapply owrWait;
  [ eapply bisim_trans; [exact Br | ovWait_timers_bisim]
  | eapply bisim_trans; [apply bisim_symm; exact Bq' | ovWait_timers_bisim]
  | exact Eu | exact Eu' | exact Emod
  | apply evalExpFunTime_time | apply evalExpFunTime_time
  | apply evalExpFunTime_time | apply evalExpFunTime_time ].

Lemma ovWaitRel_step m p q : ovWaitRel m p q ->
  forall a p', p -P- a -P> p' -> exists q', q -P- a -P> q' /\ ovWaitRel m p' q'.
Proof.
  intro R. destruct R as [p q u u' x x' y y' tu tu' tx ty Bp Bq Eu Eu' Emod Ex Ex' Ey Ey'
    | p q u u' l tu tu' Bp Bq Eu Eu' Emod | p q B].
  - (* ovWait *)
    intros a p' S. inversion S as [a0 p1 SD | d p1 SD]; subst.
    + (* a discrete step: abort, bad, the position read or the pause *)
      destruct (bisim_step_disc _ _ _ _ Bp SD) as [r [SR Br]].
      unfold ovWait in SR. invert_disc_prefixes; explicit_typed_input; output_values.
      * (* abort *)
        eassert (SR' : ovWait m u' x' y' -PA- chanAbort *? -PA> _)
          by (unfold ovWait; do 3 apply stepDpChoiceL; apply stepDpIn; typed_vals).
        destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPDisc; exact SQ | ].
        apply owrBisim. exact (bisim_trans _ _ _ Br Bq').
      * (* bad *)
        eassert (SR' : ovWait m u' x' y' -PA- chanBad *? -PA> _)
          by (unfold ovWait; do 2 apply stepDpChoiceL; apply stepDpChoiceR; apply stepDpIn;
              typed_vals).
        destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPDisc; exact SQ | ].
        apply owrBisim. exact (bisim_trans _ _ _ Br Bq').
      * (* the position read: y has run out, so y' has too *)
        match goal with [Ez : evalExpFunTime y = Some zeroTime |- _] =>
          rewrite Ey in Ez; injection Ez as Ez; subst ty end.
        match goal with [ |- context [chanPos ;? [basePosition ?p0]] ] =>
          eassert (SR' : ovWait m u' x' y' -PA- chanPos ;? [basePosition p0] -PA> _)
            by (unfold ovWait; apply stepDpChoiceL; apply stepDpChoiceR; apply stepDpTimeOut;
                [apply stepDpIn; typed_vals | exact Ey']) end.
        destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPDisc; exact SQ | ].
        eapply owrReady with (u := u) (u' := u'); try eassumption.
        -- eapply bisim_trans; [exact Br | ]. unfold_app_bisim.
           rewrite (subExp_eval_id _ u _ Eu). apply bisim_refl.
        -- eapply bisim_trans; [apply bisim_symm; exact Bq' | ]. unfold_app_bisim.
           rewrite (subExp_eval_id _ u' _ Eu'). apply bisim_refl.
      * (* the pause: x has run out, so x' has too *)
        match goal with [Ez : evalExpFunTime x = Some zeroTime |- _] =>
          rewrite Ex in Ez; injection Ez as Ez; subst tx end.
        eassert (SR' : ovWait m u' x' y' -PA- chanPause *! -PA> _)
          by (unfold ovWait; apply stepDpChoiceR; apply stepDpTimeOut;
              [apply stepDpOut; constructor | exact Ex']).
        destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPDisc; exact SQ | ].
        apply owrBisim. exact (bisim_trans _ _ _ Br Bq').
    + (* a delay: each timer counts down or runs out *)
      destruct (bisim_step_del _ _ _ _ Bp SD) as [r [SR Br]].
      unfold ovWait in SR. invert_del_prefixes.
      all: try (rewrite Ex in *; discriminate).
      all: try (rewrite Ey in *; discriminate).
      all: rewrite Ex in *; rewrite Ey in *.
      all: repeat match goal with [E : Some ?a = Some ?b |- _] =>
        injection E as E; symmetry in E; subst end.
      * (* both run out *)
        match goal with [H1 : Rplus _ _ = Rplus _ _ |- _] =>
          assert (ED : tx +dt+ d = ty +dt+ d0) by (apply delayEqR; simpl; exact H1) end.
        eassert (SR' : ovWait m u' x' y' -PD- ty +dt+ d0 -PD> _).
        { unfold ovWait. apply stepTpSum; [apply stepTpSum; [apply stepTpSum | ] | ].
          - apply stepTpIn.
          - apply stepTpIn.
          - apply stepTpDelAdd; [apply stepTpIn | exact Ey'].
          - rewrite <- ED. apply stepTpDelAdd; [apply stepTpOut | exact Ex']. }
        destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPTimed; exact SQ | ].
        close_wait Br Bq' Eu Eu' Emod.
      * (* y runs out, x counts down *)
        eassert (SR' : ovWait m u' x' y' -PD- ty +dt+ d0 -PD> _).
        { unfold ovWait. apply stepTpSum; [apply stepTpSum; [apply stepTpSum | ] | ].
          - apply stepTpIn.
          - apply stepTpIn.
          - apply stepTpDelAdd; [apply stepTpIn | exact Ey'].
          - eapply stepTpDelSub; exact Ex'. }
        destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPTimed; exact SQ | ].
        close_wait Br Bq' Eu Eu' Emod.
      * (* x runs out, y counts down *)
        eassert (SR' : ovWait m u' x' y' -PD- tx +dt+ d0 -PD> _).
        { unfold ovWait. apply stepTpSum; [apply stepTpSum; [apply stepTpSum | ] | ].
          - apply stepTpIn.
          - apply stepTpIn.
          - eapply stepTpDelSub; exact Ey'.
          - apply stepTpDelAdd; [apply stepTpOut | exact Ex']. }
        destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPTimed; exact SQ | ].
        close_wait Br Bq' Eu Eu' Emod.
      * (* both count down *)
        eassert (SR' : ovWait m u' x' y' -PD- d -PD> _).
        { unfold ovWait. apply stepTpSum; [apply stepTpSum; [apply stepTpSum | ] | ].
          - apply stepTpIn.
          - apply stepTpIn.
          - eapply stepTpDelSub; exact Ey'.
          - eapply stepTpDelSub; exact Ex'. }
        destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
        exists q'. split; [apply stepPTimed; exact SQ | ].
        close_wait Br Bq' Eu Eu' Emod.
  - (* ovReady: it broadcasts, into ovWait with the timers computed from its own *)
    intros a p' S. inversion S as [a0 p1 SD | d p1 SD]; subst.
    + destruct (bisim_step_disc _ _ _ _ Bp SD) as [r [SR Br]].
      unfold ovReady in SR. invert_disc_prefixes; output_values.
      eassert (SR' : ovReady m u' l -PA- chanOutProc ;! [baseMode m, basePosition l] -PA> _)
        by (unfold ovReady; apply stepDpOut; repeat constructor).
      destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
      exists q'. split; [apply stepPDisc; exact SQ | ].
      eapply owrWait with (u := u (-) ePeriod m) (u' := u' (-) ePeriod m)
        (x := u (-) ePeriod m) (x' := u' (-) ePeriod m) (y := ePeriod m) (y' := ePeriod m)
        (tu := mkTime (time tu -nn- time (period m)))
        (tu' := mkTime (time tu' -nn- time (period m)))
        (tx := mkTime (time tu -nn- time (period m))) (ty := period m).
      * eapply bisim_trans; [exact Br | ]. unfold_app_bisim. apply bisim_refl.
      * eapply bisim_trans; [apply bisim_symm; exact Bq' | ]. unfold_app_bisim.
        apply bisim_refl.
      * apply evalExpFunTime_subtract_period. exact Eu.
      * apply evalExpFunTime_subtract_period. exact Eu'.
      * simpl. rewrite Emod. reflexivity.
      * apply evalExpFunTime_subtract_period. exact Eu.
      * rewrite Emod. apply evalExpFunTime_subtract_period. exact Eu'.
      * apply evalExpFunTime_period.
      * apply evalExpFunTime_period.
    + destruct (bisim_step_del _ _ _ _ Bp SD) as [r [SR Br]].
      unfold ovReady in SR. invert_del_prefixes.
      eassert (SR' : ovReady m u' l -PD- d -PD> _) by (unfold ovReady; apply stepTpOut).
      destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ Bq) SR') as [q' [SQ Bq']].
      exists q'. split; [apply stepPTimed; exact SQ | ].
      eapply owrReady; [exact Br | apply bisim_symm; exact Bq' | exact Eu | exact Eu' | exact Emod].
  - (* bisimilar already *)
    intros a p' S. destruct B as [F _]. destruct (F a p' S) as [q' [S' B']].
    exists q'. split; [exact S' | apply owrBisim; exact B'].
Qed.

(** ovWait with parameters that evaluate to the same times, the first up to the period
of the mode, are bisimilar: the first parameter is only ever seen through the timers it
sets after the next broadcast, which subtract the period from it.*)
Theorem ovWait_params_bisim (m : Mode) (u u' x x' y y' : Exp) (tu tu' tx ty : Time) :
  evalExpFunTime u = Some tu -> evalExpFunTime u' = Some tu' ->
  time tu -nn- time (period m) = time tu' -nn- time (period m) ->
  evalExpFunTime x = Some tx -> evalExpFunTime x' = Some tx ->
  evalExpFunTime y = Some ty -> evalExpFunTime y' = Some ty ->
  ovWait m u x y ~p~ ovWait m u' x' y'.
Proof.
  intros. apply (bisim_coind (ovWaitRel m)).
  - intros p q R. split.
    + apply ovWaitRel_step. exact R.
    + intros a q' S. apply ovWaitRel_sym in R.
      destruct (ovWaitRel_step _ _ _ R a q' S) as [p' [S' R']].
      exists p'. split; [exact S' | apply ovWaitRel_sym; exact R'].
  - apply (owrWait m (ovWait m u x y) (ovWait m u' x' y') u u' x x' y y' tu tu' tx ty);
      first [apply bisim_refl | assumption].
Qed.

(** The timers of an ovWait that evaluate can be replaced by their values.*)
Corollary ovWaitStateExp_time (m : Mode) (u x y : Exp) (tu tx ty : Time) (p : ProcTerm) :
  evalExpFunTime u = Some tu -> evalExpFunTime x = Some tx -> evalExpFunTime y = Some ty ->
  ovWaitStateExp m u x y p -> ovWaitState m tu tx ty p.
Proof.
  intros Eu Ex Ey S. red in S |- *. eapply bisim_trans; [exact S | ].
  apply (ovWait_params_bisim m u tu x tx y ty tu tu tx ty);
    first [assumption | reflexivity | apply evalExpFunTime_time].
Qed.

(** ovWait's first parameter counts only up to the period of the mode.*)
Corollary ovWaitState_period (m : Mode) (t t' x y : Time) (p : ProcTerm) :
  time t -nn- time (period m) = time t' -nn- time (period m) ->
  ovWaitState m t x y p -> ovWaitState m t' x y p.
Proof.
  intros E S. red in S |- *. eapply bisim_trans; [exact S | ].
  apply (ovWait_params_bisim m t t' x x y y t t' x y);
    first [assumption | apply evalExpFunTime_time].
Qed.

(** An ovWait whose position timer has run out reads a position.*)
Local Lemma ovWait_pos_read_zero (m : Mode) (u x y : Exp) :
  evalExpFunTime y = Some zeroTime ->
  exists q, ovWait m u x y -PA- chanPos ;? [basePosition origin] -PA> q.
Proof.
  intro E. eexists. unfold ovWait. apply stepDpChoiceL. apply stepDpChoiceR.
  apply stepDpTimeOut; [ | exact E]. apply stepDpIn. typed_vals.
Qed.

(** Two bisimilar ovWait, the first with its position timer run out, are for the same mode, and
the second's position timer has run out too.*)
Local Lemma ovWait_bisim_mode_zero (m1 m2 : Mode) (u1 x1 y1 u2 x2 y2 : Exp) :
  evalExpFunTime y1 = Some zeroTime ->
  ovWait m1 u1 x1 y1 ~p~ ovWait m2 u2 x2 y2 ->
  m1 = m2 /\ evalExpFunTime y2 = Some zeroTime.
Proof.
  intros E1 B.
  destruct (ovWait_pos_read_zero m1 u1 x1 y1 E1) as [q1 S1].
  destruct (bisim_step_disc _ _ _ _ B S1) as [q2 [S2 BQ]].
  unfold ovWait in S1, S2. invert_disc_prefixes. clean_proc_hyp BQ.
  bt_step BQ (chanOutProc ;! [baseMode m1, basePosition origin]) S3.
  destruct (bisim_step_disc _ _ _ _ BQ S3) as [r2 [R2 _]].
  invert_app_trans. invert_disc_prefixes. output_values. split; [reflexivity | assumption].
Qed.

(** Two bisimilar ovWait, the first with a well-formed position timer, are for the same mode, and
the second's position timer is well formed too, whatever the other timers.*)
Lemma ovWait_bisim_mode (m1 m2 : Mode) (u1 x1 y1 u2 x2 y2 : Exp) (t1 : Time) :
  evalExpFunTime y1 = Some t1 ->
  ovWait m1 u1 x1 y1 ~p~ ovWait m2 u2 x2 y2 ->
  m1 = m2 /\ exists t2, evalExpFunTime y2 = Some t2.
Proof.
  intros E1 B. destruct t1 as [[r nn]].
  destruct (Rle_lt_or_eq_dec 0 r nn) as [Hlt | Heq].
  - (* delay by the timer, then the first wait reads its position *)
    set (d := mkDelay (mkposreal r Hlt)).
    assert (Hd : d <= mkTime (mknonnegreal r nn)) by (simpl; apply Rle_refl).
    unfold ovWait in B.
    match type of B with ((?A $+$ ?Bb) $+$ ($< _ >$ ?C)) $+$ ($< ?x >$ ?D) ~p~ _ =>
      destruct (taeDel d x D (taeOut d _ _ _)) as [D1 TD1];
      assert (TD : ((A $+$ Bb) $+$ ($< y1 >$ C)) $+$ ($< x >$ D) -PD- d -PD>
        (((A $+$ Bb) $+$ ($< minusTime (mkTime (mknonnegreal r nn)) d Hd >$ C)) $+$ D1))
        by (apply stepTpSum; [apply stepTpSum; [apply stepTpSum; apply stepTpIn | ] | exact TD1];
            apply stepTpDelSub; exact E1)
    end.
    destruct (bisim_step_del _ _ _ _ B TD) as [q2 [TD2 BQ]]. clear TD TD1.
    match type of BQ with ?q1 ~p~ _ =>
      eassert (S1 : q1 -PA- chanPos ;? [basePosition origin] -PA> _) end.
    { apply stepDpChoiceL. apply stepDpChoiceR. apply stepDpTimeOut.
      - apply stepDpIn. typed_vals.
      - unfold liftTimeExp. rewrite evalExpFunTime_time. f_equal. apply timeEqR. simpl. ring. }
    destruct (bisim_step_disc _ _ _ _ BQ S1) as [r2 [S2 BR]]. clear S1 BQ B.
    (* the second wait's delay and position read: its position timer was well formed *)
    invert_del_prefixes; invert_disc_prefixes; clean_proc_hyp BR.
    all: try congruence.
    all: bt_step BR (chanOutProc ;! [baseMode m1, basePosition origin]) S3;
      destruct (bisim_step_disc _ _ _ _ BR S3) as [r3 [R3 _]];
      invert_app_trans; invert_disc_prefixes; output_values; split; [reflexivity | eexists; eassumption].
  - (* the timer is zero already *)
    apply ovWait_bisim_mode_zero in B.
    + destruct B as [EQ E2]. split; [exact EQ | eexists; exact E2].
    + rewrite E1. f_equal. apply timeEqR. simpl. symmetry. exact Heq.
Qed.

(** A timer guard over a process that can delay by any amount can delay by any amount.*)
Local Lemma del_guard_any (e : Exp) (p : ProcTerm) (d : Delay) :
  (forall d', exists q, p -PD- d' -PD> q) -> exists q, $< e >$ p -PD- d -PD> q.
Proof.
  intro P. destruct (evalExpFunTime e) as [t | ] eqn:E.
  - destruct (Rle_lt_dec d t) as [LE | LT].
    + eexists. eapply stepTpDelSub with (H := LE). exact E.
    + destruct (P (minusDelay d t LT)) as [q Q]. exists q.
      rewrite (minusDelayAddTime d t LT). apply stepTpDelAdd; assumption.
  - eexists. apply stepTpDelIll. exact E.
Qed.

(** ovWait can delay by any amount.*)
Lemma ovWait_del_any m e2 e3 e4 d : exists q, ovWait m e2 e3 e4 -PD- d -PD> q.
Proof.
  unfold ovWait.
  match goal with [ |- exists q, (( _ $+$ _) $+$ $< e4 >$ ?P4) $+$ $< e3 >$ ?P3 -PD- d -PD> q ] =>
    destruct (del_guard_any e4 P4 d) as [q4 Q4]; [intro d'; eexists; apply stepTpIn | ];
    destruct (del_guard_any e3 P3 d) as [q3 Q3]; [intro d'; eexists; apply stepTpOut | ] end.
  eexists. repeat apply stepTpSum; first [apply stepTpIn | exact Q4 | exact Q3].
Qed.

(** Inverts every sort of a sum, a prefix or a timer guard in the context.*)
Local Ltac invert_sorts := repeat match goal with
  | [H : sort _ _ (sum _ _) |- _] => inversion H; clear H; subst
  | [H : sort _ _ (inPrefix _ _ _) |- _] => inversion H; clear H; subst
  | [H : sort _ _ (outPrefix _ _ _) |- _] => inversion H; clear H; subst
  | [H : sort _ _ (del _ _) |- _] => inversion H; clear H; subst
  end.

(** ovWait can read a position within d exactly when its position timer is less than d.*)
Lemma ovWait_sort_pos m e2 e3 e4 l d :
  sort (chanPos ;? [basePosition l]) d (ovWait m e2 e3 e4) <->
  exists t4, evalExpFunTime e4 = Some t4 /\ nonneg (time t4) < pos (delay d).
Proof.
  unfold ovWait. split.
  - intro S. invert_sorts. eexists. split; [eassumption | ]. simpl.
    match goal with [ |- _ < _ + pos (delay ?d0)] => pose proof (cond_pos (delay d0)) end.
    lra.
  - intros [t4 [E LT]]. rewrite (minusDelayAddTime d t4 LT).
    apply sortSumL. apply sortSumR. apply sortDel; [exact E | ]. apply sortIn. typed_vals.
Qed.

(** ovWait can pause within d exactly when its pause timer is less than d.*)
Lemma ovWait_sort_pause m e2 e3 e4 d :
  sort (chanPause *!) d (ovWait m e2 e3 e4) <->
  exists t3, evalExpFunTime e3 = Some t3 /\ nonneg (time t3) < pos (delay d).
Proof.
  unfold ovWait. split.
  - intro S. invert_sorts. eexists. split; [eassumption | ]. simpl.
    match goal with [ |- _ < _ + pos (delay ?d0)] => pose proof (cond_pos (delay d0)) end.
    lra.
  - intros [t3 [E LT]]. rewrite (minusDelayAddTime d t3 LT).
    apply sortSumR. apply sortDel; [exact E | ]. apply sortOut. constructor.
Qed.

(** Two non-negative numbers below the same delays are equal.*)
Local Lemma nonneg_eq_from_delays (r1 r2 : R) : 0 <= r1 -> 0 <= r2 ->
  (forall d : Delay, r1 < pos (delay d) <-> r2 < pos (delay d)) -> r1 = r2.
Proof.
  intros N1 N2 H. destruct (Rtotal_order r1 r2) as [LT | [EQ | GT]]; [ | exact EQ | ];
    exfalso.
  - assert (P : 0 < (r1 + r2) / 2) by lra.
    specialize (H (mkDelay (mkposreal _ P))). simpl in H. lra.
  - assert (P : 0 < (r1 + r2) / 2) by lra.
    specialize (H (mkDelay (mkposreal _ P))). simpl in H. lra.
Qed.

(** A timer that is below exactly the delays above a time t is t.*)
Local Lemma timer_from_delays (e : Exp) (t : Time) :
  (forall d : Delay, (exists t1, evalExpFunTime e = Some t1 /\ nonneg (time t1) < pos (delay d))
    <-> nonneg (time t) < pos (delay d)) ->
  evalExpFunTime e = Some t.
Proof.
  intro H. destruct (proj2 (H (t +dt+ mkDelay onePos))) as [t1 [E LT]];
    [simpl; pose proof (cond_pos onePos); lra | ].
  rewrite E. f_equal. apply timeEqR. apply nonneg_eq_from_delays; [timeNonneg | timeNonneg | ].
  intro d. rewrite <- (H d). split.
  - intro L. exists t1. split; [exact E | exact L].
  - intros [t2 [E2 L2]]. rewrite E in E2. injection E2 as E2. subst. exact L2.
Qed.

(** Of two bisimilar ovWait, the first's position timer is the time the second's is.*)
Lemma ovWait_bisim_pos_timer m1 u1 x1 y1 m2 u2 x2 y2 t :
  ovWait m1 u1 x1 y1 ~p~ ovWait m2 u2 x2 y2 -> evalExpFunTime y2 = Some t ->
  evalExpFunTime y1 = Some t.
Proof.
  intros B E. apply timer_from_delays. intro d.
  rewrite <- (ovWait_sort_pos m1 u1 x1 y1 origin d).
  rewrite (bisim_sort_iff _ _ _ d B (ovWait_del_any _ _ _ _ d)).
  rewrite (ovWait_sort_pos m2 u2 x2 y2 origin d). split.
  - intros [t2 [E2 L2]]. rewrite E in E2. injection E2 as E2. subst. exact L2.
  - intro L. exists t. split; [exact E | exact L].
Qed.

(** Of two bisimilar ovWait, the first's pause timer is the time the second's is.*)
Lemma ovWait_bisim_pause_timer m1 u1 x1 y1 m2 u2 x2 y2 t :
  ovWait m1 u1 x1 y1 ~p~ ovWait m2 u2 x2 y2 -> evalExpFunTime x2 = Some t ->
  evalExpFunTime x1 = Some t.
Proof.
  intros B E. apply timer_from_delays. intro d.
  rewrite <- (ovWait_sort_pause m1 u1 x1 y1 d).
  rewrite (bisim_sort_iff _ _ _ d B (ovWait_del_any _ _ _ _ d)).
  rewrite (ovWait_sort_pause m2 u2 x2 y2 d). split.
  - intros [t2 [E2 L2]]. rewrite E in E2. injection E2 as E2. subst. exact L2.
  - intro L. exists t. split; [exact E | exact L].
Qed.

(** Two bisimilar ovWait, the second with a well-formed position timer, delay into two
bisimilar ovWait with the same first two parameters, the second's position timer run out.*)
Lemma ovWait_bisim_pos_timeout m1 u1 x1 y1 m2 u2 x2 y2 t :
  ovWait m1 u1 x1 y1 ~p~ ovWait m2 u2 x2 y2 -> evalExpFunTime y2 = Some t ->
  exists x1' y1' x2' y2', ovWait m1 u1 x1' y1' ~p~ ovWait m2 u2 x2' y2' /\
    evalExpFunTime y2' = Some zeroTime.
Proof.
  intros B E. destruct (Rle_lt_or_eq_dec 0 t (cond_nonneg t)) as [LT | EQ].
  - set (d := mkDelay (mkposreal _ LT)).
    destruct (ovWait_del_any m2 u2 x2 y2 d) as [b' DB].
    destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ B) DB) as [a' [DA BAB]].
    destruct (ovWait_del_shape _ _ _ _ _ _ DB) as [e3b [e4b BB]].
    destruct (ovWait_del_shape _ _ _ _ _ _ DA) as [e3a [e4a BA]].
    exists e3a e4a e3b e4b. split.
    + eapply bisim_trans; [apply bisim_symm; exact BA | ].
      eapply bisim_trans; [apply bisim_symm; exact BAB | exact BB].
    + apply timer_from_delays. intro d'.
      rewrite <- (ovWait_sort_pos m2 u2 e3b e4b origin d').
      rewrite (bisim_sort_iff _ _ _ d' (bisim_symm _ _ BB) (ovWait_del_any _ _ _ _ d')).
      rewrite (sortDerivEquiv _ _ _ _ _ DB). rewrite (ovWait_sort_pos m2 u2 x2 y2 origin).
      simpl. split.
      * intros _. pose proof (cond_pos (delay d')). lra.
      * intros _. exists t. split; [exact E | ]. simpl. pose proof (cond_pos (delay d')). lra.
  - exists x1 y1 x2 y2. split; [exact B | ]. rewrite E. f_equal. apply timeEqR.
    simpl. symmetry. exact EQ.
Qed.

(** ovWaitN applied to its arguments is ovWait with its pause timer set to its first
parameter.*)
Lemma ovWaitN_bisim (m : Mode) (e2 e4 : Exp) :
  ovWaitN $( [eBase (baseMode m), e2, e4] )$ ~p~ ovWait m e2 e2 e4.
Proof. unfold_app_bisim. apply bisim_refl. Qed.

(** ovReady's only step is its broadcast, into ovWait with its timer less the period as first
parameter and pause timer, and the period as position timer.*)
Lemma ovReady_step_ovWait (m : Mode) (u : Exp) (l : Position) b q :
  ovReady m u l -PA- b -PA> q ->
  b = chanOutProc ;! [baseMode m, basePosition l] /\
  q ~p~ ovWait m (u (-) ePeriod m) (u (-) ePeriod m) (ePeriod m).
Proof.
  intro S. unfold ovReady in S. invert_disc_prefixes. output_values. split; [reflexivity | ].
  unfold_app_bisim. apply bisim_refl.
Qed.

(** After a step into switchCurr, the overlap component was switchBc.*)
Theorem switchCurr_prev (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> overlapState p -> switchCurrState p' ->
  exists m, switchBcState m p.
Proof.
  intros TR O SP. red in SP. backtrack_shape SP.
  eexists. exact B.
Qed.

(*** Fwd tracking ***)

(** Results **)




(*
(Tatic definition is to go in above tactics section)
-Idea for fwd-tracking tactic:
>First assert and name a new hypothesis equivalent to the LHS of the goal
=>(match exists xs, P /\ Q and assert exists xs, P)
>Then repeat eexists
>Then apply an activation tactic
>Then remove existentials from the newly asserted hypothesis (maybe a tactic to do this-
maybe it already exists, has to work for arbitrary number of variables,
don't worry about naming the variables)
>Then repeat eexists
>Then split the goal
>Apply the asserted hypothesis to the LHS
>Apply state_trans_src, strengthening the asserted hypothesis
>From here perform a number of inversions (invert_trans?) and you should have something
very close to your goal
>Potentially use the tactics below as a template
>Potentially use tactics developed for listening_inProc e.g. fwd_track_pre

Ltac activation_pre_tac :=
  intro X; invertClear X;
  [eapply daeApp; [reflexivity | simpl] |
  match goal with
  | [Q : ?pred ?x1 ?x2 ?x3 = ?proc |- _] => unfold pred
  | [Q : ?pred ?x1 ?x2 = ?proc |- _] => unfold pred
  | [Q : ?pred ?x1 = ?proc |- _] => unfold pred
  | [Q : ?pred = ?proc |- _] => unfold pred
  end].

Ltac activation_post_tac :=
  match goal with
  [ |- discActEnabled ?p ?a] => 
    match p with
    (*For sum, recursively go left and see if it succeeds, else go right.*)
    | _ $< _ >$ ? _  => apply dae_inPfx; typed_vals
    | _ $< _ >$ ! _  => apply dae_outPfx; constructor
    | ?p1 $+$ ?p2 => first [solve [apply daeSumL; activation_post_tac] |
      solve [apply daeSumR; activation_post_tac]]
    end
  end.
*)

(*** Conditional fwd tracking ***)
(* Hopefully I can copy the tactics for regular forward tracking, or even use them.
If I'm clever I'll make the tactics as modular as possible, allowing them to be
reused in multiple places. For example, there should be one tactic to do all the
pre-processing and get rid of all the contradictary cases. Then after this tactic,
another tactic sweeps in and solves the goal directly from the hypotheses- a
disjunction is not a big problem here, a regular old "assumption" might even
work, or if not I'm sure there's a tactic for this. The main work anyway is
inversions and eliminations of contradictory cases.*)

(* begin helpers for currOK_next *)
(** Rewrites a goal [app N args ~p~ T] into [body[args/vars] ~p~ T], with the
substitution computed away. *)
Ltac currOK_next_unfold_app :=
  eapply bisim_trans; [apply app_bisim | ];
  cbn [unfoldApp def protocolDefs protocolDef fst snd listsToSub liftVarList liftExpList subProcTerm
    subExp subBoolExp listSub map liftNameProc listBaselistExp
    bcWait sleeping bcReady dormant init ovWait ovReady switchBc switchCurr
    switchListen tfsStart tfsNext tfsCurr tfsBc tfsListen ovAbort listening
    checkRange rangeBad currEq badOvlp currOK nextEq abortOvlp gotMsg gotRange
    currPincCheck currComp nextPincCheck paused];
  remove_updates.

(** Closes a goal [listeningN $( [] )$ ~p~ listening]. *)
Ltac currOK_next_listening_app := apply app_bisim_nil; reflexivity.

(** Pre-processing for forward tracking: from [TR : p -PA- a -PA> p'] and a simple
state predicate [p ~p~ X] in the context, generates all transitions of [X]
and leaves the goal with [p' ~p~ D] for each derivative [D]. *)
Ltac currOK_next_fwd_pre :=
  match goal with [S : ?p ~p~ _, TR : ?p -PA- _ -PA> _ |- _] =>
    let q := fresh "q" in let TQ := fresh "TQ" in let B := fresh "B" in
    destruct (bisim_step_disc _ _ _ _ S TR) as [q [TQ B]] end;
  invert_disc_prefixes; explicit_typed_input;
  cbn [listsToSub liftVarList liftExpList listBaselistExp map subProcTerm listSub
    liftNameProc subExp] in *;
  repeat match goal with [H : _ ~p~ _ |- _] => remove_updates_hyp H end.
(* end helpers *)

Theorem currOK_next (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  p -PA- a -PA> p' -> currOKState m'' p ->
  (exists m, nextEqState m m'' p') \/
  listeningState p'.
Proof.
  intros TR CS. unfold currOKState in CS. unfold currOK in CS.
  currOK_next_fwd_pre.
  - right. unfold listeningState. eapply bisim_trans; [eassumption | ].
    currOK_next_listening_app.
  - left. eexists. unfold nextEqState. eapply bisim_trans; [eassumption | ].
    currOK_next_unfold_app. apply bisim_refl.
Qed.

(** The same, with the action: currOK reads stable, into listening, or reads a next mode,
into nextEq with it.*)
Lemma currOK_next_act (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  p -PA- a -PA> p' -> currOKState m'' p ->
  (a = chanMStableRead *? /\ listeningState p') \/
  (exists m, a = chanMNextRead ;? [baseMode m] /\ nextEqState m m'' p').
Proof.
  intros TR CS. unfold currOKState in CS. unfold currOK in CS.
  currOK_next_fwd_pre.
  - left. split; [reflexivity | ]. unfold listeningState.
    eapply bisim_trans; [eassumption | ]. currOK_next_listening_app.
  - right. eexists. split; [reflexivity | ]. unfold nextEqState.
    eapply bisim_trans; [eassumption | ]. currOK_next_unfold_app. apply bisim_refl.
Qed.

Theorem rangeBad_next (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  p -PA- a -PA> p' -> rangeBadState m'' p ->
  (exists m, currEqState m m'' p').
Proof.
  intros TR CS. unfold rangeBadState in CS. unfold rangeBad in CS.
  currOK_next_fwd_pre.
  eexists. unfold currEqState. eapply bisim_trans; [eassumption | ].
  currOK_next_unfold_app. apply bisim_refl.
Qed.

(** The same, with the action: the only step of rangeBad reads a mode on mCurr.*)
Lemma rangeBad_next_act (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  p -PA- a -PA> p' -> rangeBadState m'' p ->
  exists m, a = chanMCurrRead ;? [baseMode m] /\ currEqState m m'' p'.
Proof.
  intros TR CS. unfold rangeBadState in CS. unfold rangeBad in CS.
  currOK_next_fwd_pre.
  eexists. split; [reflexivity | ]. unfold currEqState.
  eapply bisim_trans; [eassumption | ]. currOK_next_unfold_app. apply bisim_refl.
Qed.

(** A conditional of the protocol's form matters only through the value of its condition and
its branches.*)
Lemma cond_branches_bisim b1 b2 p p' q q' :
  evalBoolExpFun b1 = evalBoolExpFun b2 -> p ~p~ p' -> q ~p~ q' ->
  b1 $> p $+$ !~ b1 $> q ~p~ b2 $> p' $+$ !~ b2 $> q'.
Proof.
  intros E P Q. destruct (evalBoolExpFun b1) as [[ | ] | ] eqn:E1.
  - eapply bisim_trans; [apply if_then_bisim_true; apply evalBoolExpFunRel; exact E1 | ].
    eapply bisim_trans; [exact P | ]. apply bisim_symm.
    apply if_then_bisim_true; apply evalBoolExpFunRel; rewrite <- E; reflexivity.
  - eapply bisim_trans; [apply if_then_bisim_false; apply evalBoolExpFunRel; exact E1 | ].
    eapply bisim_trans; [exact Q | ]. apply bisim_symm.
    apply if_then_bisim_false; apply evalBoolExpFunRel; rewrite <- E; reflexivity.
  - eapply bisim_trans; [apply if_then_bisim_none; exact E1 | ]. apply bisim_symm.
    apply if_then_bisim_none. rewrite <- E. reflexivity.
Qed.

(** gotRange shows its range only through the threat tests of currPincCheck and nextPincCheck,
against the modes it reads. So two gotRange whose ranges are closed and pass the same tests
are bisimilar.*)
Lemma gotRange_threat_bisim (m : Mode) (e e' : Exp) (b b' : BaseValue) :
  evalExpFun e = Some b -> evalExpFun e' = Some b' ->
  (forall v : Mode, evalBoolExpFun (bPossInc v m e) = evalBoolExpFun (bPossInc v m e')) ->
  gotRange m e ~p~ gotRange m e'.
Proof.
  intros Ee Ee' P.
  (* gotRange reads the current mode, into currPincCheck *)
  unfold gotRange. apply inPrefix_bisim_context. intros vs T.
  explicit_typed_input. clean_proc.
  rewrite (eval_pres_sub e b _ (evalExpFunRel _ _ Ee)).
  rewrite (eval_pres_sub e' b' _ (evalExpFunRel _ _ Ee')).
  unfold_app_bisim. apply bisim_symm. unfold_app_bisim. apply bisim_symm.
  eapply bisim_trans; [apply choice_bisim_symm | ].
  eapply bisim_trans; [ | apply choice_bisim_symm].
  apply cond_branches_bisim; [apply P | apply bisim_refl | ].
  (* currComp reads stable, into listening, or a next mode, into nextPincCheck *)
  unfold_app_bisim. apply bisim_symm. unfold_app_bisim. apply bisim_symm.
  apply choice_bisim_context; [apply bisim_refl | ].
  apply inPrefix_bisim_context. intros vs T. explicit_typed_input. clean_proc.
  rewrite (eval_pres_sub e b _ (evalExpFunRel _ _ Ee)).
  rewrite (eval_pres_sub e' b' _ (evalExpFunRel _ _ Ee')).
  unfold_app_bisim. apply bisim_symm. unfold_app_bisim. apply bisim_symm.
  eapply bisim_trans; [apply choice_bisim_symm | ].
  eapply bisim_trans; [ | apply choice_bisim_symm].
  apply cond_branches_bisim; [apply P | apply bisim_refl | apply bisim_refl].
Qed.

(** A time evaluates to the number it holds.*)
Lemma evalBaseNonnegFun_time (t : Time) : evalBaseNonnegFun (baseTime t) = Some (time t).
Proof. destruct t. reflexivity. Qed.

(** The step of gotMsg m'' l reads a position v, into gotRange with the range computed from
it.*)
Lemma gotMsg_next_act (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) (l : Position) :
  p -PA- a -PA> p' -> gotMsgState m'' l p ->
  exists v, a = chanPos ;? [basePosition v] /\
    gotRangeState m'' (mkDistance (dist2d v l -nn- speedMax *nn* msgLatency)) p'.
Proof.
  intros TR GS. unfold gotMsgState in GS.
  destruct (bisim_step_disc _ _ _ _ GS TR) as [q [TQ B]].
  unfold gotMsg in TQ. invert_disc_prefixes. explicit_typed_input. clean_proc_hyp B.
  eexists. split; [reflexivity | ].
  unfold gotRangeState. eapply bisim_trans; [exact B | ]. unfold_app_bisim.
  eapply gotRange_threat_bisim; [ | reflexivity | ].
  - cbn [evalExpFun]. rewrite evalBaseNonnegFun_time. reflexivity.
  - intro v. cbn [evalBoolExpFun evalExpFun]. rewrite evalBaseNonnegFun_time. reflexivity.
Qed.

(** The steps of currComp: it reads stable, into listening, or a next mode, into
nextPincCheck with it.*)
Lemma currComp_next_act (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) (r : Distance) :
  p -PA- a -PA> p' -> currCompState m'' r p ->
  (a = chanMStableRead *? /\ listeningState p') \/
  (exists m, a = chanMNextRead ;? [baseMode m] /\ nextPincCheckState m m'' r p').
Proof.
  intros TR CS. unfold currCompState in CS. unfold currComp in CS.
  currOK_next_fwd_pre.
  - left. split; [reflexivity | ]. unfold listeningState.
    eapply bisim_trans; [eassumption | ]. currOK_next_listening_app.
  - right. eexists. split; [reflexivity | ]. unfold nextPincCheckState.
    eapply bisim_trans; [eassumption | ]. currOK_next_unfold_app. apply bisim_refl.
Qed.

Theorem gotMessage_next (p p' : ProcTerm)
  (a : DiscAct) (m'' : Mode) (l : Position) :
  p -PA- a -PA> p' -> gotMsgState m'' l p ->
  (exists r, gotRangeState m'' r p').
Proof.
  intros TR GS. destruct (gotMsg_next_act _ _ _ _ _ TR GS) as [v [_ GR]]. eexists. exact GR.
Qed.

Theorem gotRange_next (p p' : ProcTerm)
  (a : DiscAct) (m'' : Mode) (r : Distance) :
  p -PA- a -PA> p' -> gotRangeState m'' r p ->
  (exists m, currPincCheckState m m'' r p').
Proof.
  intros TR CS. unfold gotRangeState in CS. unfold gotRange in CS.
  currOK_next_fwd_pre.
  eexists. unfold currPincCheckState. eapply bisim_trans; [eassumption | ].
  currOK_next_unfold_app. apply bisim_refl.
Qed.

(** The same, with the action: the only step of gotRange reads a mode on mCurr.*)
Lemma gotRange_next_act (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) (r : Distance) :
  p -PA- a -PA> p' -> gotRangeState m'' r p ->
  exists m, a = chanMCurrRead ;? [baseMode m] /\ currPincCheckState m m'' r p'.
Proof.
  intros TR CS. unfold gotRangeState in CS. unfold gotRange in CS.
  currOK_next_fwd_pre.
  eexists. split; [reflexivity | ]. unfold currPincCheckState.
  eapply bisim_trans; [eassumption | ]. currOK_next_unfold_app. apply bisim_refl.
Qed.

Theorem currComp_next (p p' : ProcTerm)
  (a : DiscAct) (m'' : Mode) (r : Distance) :
  p -PA- a -PA> p' -> currCompState m'' r p ->
  (exists m, nextPincCheckState m m'' r p') \/
  listeningState p'.
Proof.
  intros TR CS. unfold currCompState in CS. unfold currComp in CS.
  currOK_next_fwd_pre.
  - right. unfold listeningState. eapply bisim_trans; [eassumption | ].
    currOK_next_listening_app.
  - left. eexists. unfold nextPincCheckState. eapply bisim_trans; [eassumption | ].
    currOK_next_unfold_app. apply bisim_refl.
Qed.

Theorem badOvlp_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> badOvlpState p -> listeningState p'.
Proof.
  intros TR CS. unfold badOvlpState in CS. unfold badOvlp in CS.
  currOK_next_fwd_pre.
  unfold listeningState. eapply bisim_trans; [eassumption | ].
  currOK_next_listening_app.
Qed.

Theorem abortOvlp_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> abortOvlpState p -> listeningState p'.
Proof.
  intros TR CS. unfold abortOvlpState in CS. unfold abortOvlp in CS.
  currOK_next_fwd_pre.
  unfold listeningState. eapply bisim_trans; [eassumption | ].
  currOK_next_listening_app.
Qed.

Lemma tfsStart_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> tfsStartState p ->
  exists m, tfsNextState m p'.
Proof.
  intros TR CS. unfold tfsStartState in CS. unfold tfsStart in CS.
  currOK_next_fwd_pre.
  eexists. unfold tfsNextState. eapply bisim_trans; [eassumption | ].
  currOK_next_unfold_app. apply bisim_refl.
Qed.

(** The same, with the action: the only step of tfsStart reads a mode on mCurr.*)
Lemma tfsStart_next_act (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> tfsStartState p ->
  exists m, a = chanMCurrRead ;? [baseMode m] /\ tfsNextState m p'.
Proof.
  intros TR CS. unfold tfsStartState in CS. unfold tfsStart in CS.
  currOK_next_fwd_pre.
  eexists. split; [reflexivity | ]. unfold tfsNextState.
  eapply bisim_trans; [eassumption | ]. currOK_next_unfold_app. apply bisim_refl.
Qed.

(** The steps of tfsNext: it writes the fail-safe successor of its mode on mNext and moves to
tfsCurr, or writes on mStable and stays.*)
Lemma tfsNext_next_act (p p' : ProcTerm) (a : DiscAct) (m : Mode) :
  p -PA- a -PA> p' -> tfsNextState m p ->
  (a = chanMNextWrite ;! [baseMode (failSafeSucc m)] /\ tfsCurrState p') \/
  (a = chanMStableWrite *! /\ tfsNextState m p').
Proof.
  intros T B. destruct (bisim_step_disc _ _ _ _ B T) as [q [TQ BQ]].
  unfold tfsNext in TQ. invert_disc_prefixes;
  repeat match goal with
    | [H : evalExpLists _ _ |- _] => inversion H; subst; clear H
    | [H : evalExp (eFailSafeSucc _) _ |- _] => inversion H; subst; clear H
    | [H : evalExp (eBase _) _ |- _] => inversion H; subst; clear H end.
  - left. split; [reflexivity | ]. red. eapply bisim_trans; [exact BQ | ].
    apply app_bisim_nil; reflexivity.
  - right. split; [reflexivity | ]. red. eapply bisim_trans; [exact BQ | ].
    unfold_app_bisim. apply bisim_refl.
Qed.

(** The steps of tfsCurr: it switches mode on mCurr and moves to tfsBc, or takes an abort or a
bad and stays.*)
Lemma tfsCurr_next_act (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> tfsCurrState p ->
  (a = chanMCurrWrite *! /\ tfsBcState p') \/ tfsCurrState p'.
Proof.
  intros T B. destruct (bisim_step_disc _ _ _ _ B T) as [q [TQ BQ]].
  unfold tfsCurr in TQ. invert_disc_prefixes; explicit_typed_input; clean_proc_hyp BQ;
  repeat match goal with [H : evalExpLists [] _ |- _] => inversion H; subst; clear H end;
  (first [left; split; [reflexivity | ] | right]); red;
  (eapply bisim_trans; [exact BQ | apply app_bisim_nil; reflexivity]).
Qed.
  
(****************** Conditionals ******************)
(* In here are resuls relating conditional state predicates to their branches.
In general, the results are of the form "If some conditional state predicate S
is true, and the condition is true (say), then the state predicate S' corresponding
to the true branch of S is true"*)

Lemma currEq_cond_true m m'' p :
  m = m'' -> currEqState m m'' p -> badOvlpState p.
Proof.
  intros E S. unfold currEqState, badOvlpState in *. subst m''.
  assert (B : evalBoolExp (m =b= m) true)
    by (eapply bevalEqualTrue; apply evalBase).
  eapply bisim_trans. apply S. unfold currEq.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  apply app_bisim_nil; reflexivity.
Qed.

Lemma currEq_cond_false m m'' p :
  m <> m'' -> currEqState m m'' p -> currOKState m'' p.
Proof.
  intros NE S. unfold currEqState, currOKState in *.
  assert (B : evalBoolExp (m =b= m'') false).
  { eapply bevalEqualFalse; [apply evalBase | apply evalBase | ].
    intro E. inversion E. contradiction. }
  eapply bisim_trans. apply S. unfold currEq.
  eapply bisim_trans. apply (if_then_bisim_false _ _ _ B).
  eapply bisim_trans; [apply app_bisim_def; reflexivity | ]. clean_proc. apply bisim_refl.
Qed.

Lemma nextEq_cond_true m' m'' p :
  m' = m'' -> nextEqState m' m'' p -> abortOvlpState p.
Proof.
  intros E S. unfold nextEqState, abortOvlpState in *. subst m''.
  assert (B : evalBoolExp (m' =b= m') true)
    by (eapply bevalEqualTrue; apply evalBase).
  eapply bisim_trans. apply S. unfold nextEq.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  apply app_bisim_nil; reflexivity.
Qed.

Lemma nextEq_cond_false m' m'' p :
  m' <> m'' -> nextEqState m' m'' p -> listeningState p.
Proof.
  intros NE S. unfold nextEqState, listeningState in *.
  assert (B : evalBoolExp (m' =b= m'') false).
  { eapply bevalEqualFalse; [apply evalBase | apply evalBase | ].
    intro E. inversion E. contradiction. }
  eapply bisim_trans. apply S. unfold nextEq.
  eapply bisim_trans. apply (if_then_bisim_false _ _ _ B).
  apply app_bisim_nil; reflexivity.
Qed.

Lemma currPincCheck_cond_true m m'' (r : Distance) p :
  possiblyIncompatible m m'' r -> currPincCheckState m m'' r p ->
  badOvlpState p.
Proof.
  intros PI S. unfold currPincCheckState, badOvlpState in *.
  assert (B : evalBoolExp (bPossInc m m'' r) true).
  { rewrite <- (possInc_possIncBool m m'' r PI).
    apply bevalPossInc_dist; apply evalBase. }
  eapply bisim_trans. apply S. unfold currPincCheck.
  eapply bisim_trans. apply choice_bisim_symm.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  apply app_bisim_nil; reflexivity.
Qed.

Lemma currPincCheck_cond_false m m'' (r : Distance) p :
  ~possiblyIncompatible m m'' r ->
  currPincCheckState m m'' r p -> currCompState m'' r p.
Proof.
  intros NPI S. unfold currPincCheckState, currCompState in *.
  assert (B : evalBoolExp (bPossInc m m'' r) false).
  { assert (F : possIncBool m m'' r = false).
    { unfold possIncBool. destruct (possIncDec m m'' r);
      [contradiction | reflexivity]. }
    rewrite <- F. apply bevalPossInc_dist; apply evalBase. }
  eapply bisim_trans. apply S. unfold currPincCheck.
  eapply bisim_trans. apply choice_bisim_symm.
  eapply bisim_trans. apply (if_then_bisim_false _ _ _ B).
  eapply bisim_trans; [apply app_bisim_def; reflexivity | ]. clean_proc. apply bisim_refl.
Qed.

Lemma nextPincCheck_cond_true m m'' (r : Distance) p :
  possiblyIncompatible m m'' r ->
  nextPincCheckState m m'' r p -> abortOvlpState p.
Proof.
  intros PI S. unfold nextPincCheckState, abortOvlpState in *.
  assert (B : evalBoolExp (bPossInc m m'' r) true).
  { rewrite <- (possInc_possIncBool m m'' r PI).
    apply bevalPossInc_dist; apply evalBase. }
  eapply bisim_trans. apply S. unfold nextPincCheck.
  eapply bisim_trans. apply choice_bisim_symm.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  apply app_bisim_nil; reflexivity.
Qed.

Lemma nextPincCheck_cond_false m m'' (r : Distance) p :
  ~possiblyIncompatible m m'' r ->
  nextPincCheckState m m'' r p -> listeningState p.
Proof.
  intros NP U. red in U. red.
  assert (PB : possIncBool m m'' r = false).
  { unfold possIncBool. destruct (possIncDec m m'' r); [contradiction | reflexivity]. }
  destruct r as [r].
  eapply bisim_trans; [exact U | ].
  unfold nextPincCheck.
  eapply bisim_trans.
  { apply choice_bisim_context.
    - apply cond_bisim_true. change true with (negb false). apply bevalNot.
      rewrite <- PB. apply bevalPossInc_dist; constructor.
    - apply cond_bisim_false. unfold evalBoolExpFunTot. simpl.
      first [exact PB | rewrite PB; reflexivity]. }
  eapply bisim_trans; [apply choice_bism_unit_r | ].
  apply app_bisim_nil; reflexivity.
Qed.

(****************** Delay Preservation ******************)

(*NOTE- IN HERE WE ACTUALLY WANT BACKWARDS AND FORWARDS PRESERVATION
EITHER DO SEPARATE THEOREMS FOR EACH, AND ADD BACK AND FWD TO RESULT
NAMES, OR DO BOTH IN ONE THEOREM, USING THE <-> OPERATOR.*)

(**In this section, we would like to collect a number of results asserting
that the delay relation preserves certain state predicates. Here we will
write a few examples, but there is no need to write out all the cases,
especially since the way these things are defined might change. Just
enough to get a general idea.*)

(*** Simple Predicate Preservation ***)

(** A delay keeps the overlap component waiting for the same mode and wait time. Only its two
timers change: they count down until they run out.*)
Lemma ovWait_del_pres m t x y p p' d :
  ovWaitState m t x y p -> p -PD- d -PD> p' ->
  exists x' y', ovWaitState m t x' y' p'.
Proof.
  intros U V. destruct (bisim_step_del _ _ _ _ U V) as [q [W B]].
  unfold ovWait in W.
  (*The two input prefixes delay to themselves, and each timer delays to some timer.*)
  repeat match goal with
    | [H : _ $+$ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    | [H : _ $< _ >$ ? _ -PD- _ -PD> _ |- _] => apply del_self_inPrefix in H; subst
    end.
  match goal with [HC : $< _ >$ (_ $< _ >$ ? _) -PD- _ -PD> _ |- _] =>
    destruct (del_del_bisim _ _ _ _ _ (evalExpFunTime_time _) (del_self_inPrefix _ _ _) HC)
    as [y' BC] end.
  match goal with [HD : $< _ >$ (_ $< _ >$ ! _) -PD- _ -PD> _ |- _] =>
    destruct (del_del_bisim _ _ _ _ _ (evalExpFunTime_time _) (del_self_outPrefix _ _ _) HD)
    as [x' BD] end.
  exists x'. exists y'. unfold ovWaitState, ovWait.
  eapply bisim_trans; [exact B | ].
  repeat apply choice_bisim_context; first [apply bisim_refl | assumption].
Qed.

Lemma ovReady_del_pres m t l p p' d :
  ovReadyState m t l p -> p -PD- d -PD> p' ->
  ovReadyState m t l p'.
Proof.
  unfold ovReadyState, ovReady. intros.
  eapply bisim_del_pres; [del_self_tac | eassumption | eassumption].
Qed.

Lemma switchBc_del_pres m p p' d :
  switchBcState m p -> p -PD- d -PD> p' ->
  switchBcState m p'.
Proof.
  unfold switchBcState, switchBc. intros.
  eapply bisim_del_pres; [del_self_tac | eassumption | eassumption].
Qed.

Lemma switchCurr_del_pres p p' d :
  switchCurrState p -> p -PD- d -PD> p' ->
  switchCurrState p'.
Proof.
  unfold switchCurrState, switchCurr. intros.
  eapply bisim_del_pres; [del_self_tac | eassumption | eassumption].
Qed.

(*** Compound Predicate Preservation ***)

(**The delay relation preserves the nextSinceState predicate.*)
Theorem del_pres_nextSinceState (p p' : ProcTerm) (d : Delay) : 
  nextSinceState p -> p -PD- d -PD> p' -> nextSinceState p'.
  (*Proof: Inversion on nextSinceState into all possible cases*)
  introz U. inversion U.
  (*Now simply apply delay preservation results on these.*)
  destruct (ovWait_del_pres _ _ _ _ _ _ _ H U0) as [x' [y' AUX]]. eapply nexsOvwSt; eassumption.
  lets AUX : ovReady_del_pres H U0. eapply nexsOvrSt; eassumption.
  lets AUX : switchBc_del_pres H U0. eapply nexsSbcSt; eassumption.
  lets AUX : switchCurr_del_pres H U0. eapply nexsScSt; eassumption.
  Qed.

(**The delay relation preserves the tfsState predicate.*)
Theorem del_pres_tfsState (p p' : ProcTerm) (d : Delay): 
  tfsState p -> p -PD- d -PD> p' -> tfsState p'.
Proof.
  intros U V. destruct U as [H|m H|H|H|H];
    [apply tfsStaSt | apply (tfsNexSt _ m) | apply tfsCurSt | apply tfsBcSt |
     apply tfsLisSt];
    unfold tfsStartState, tfsNextState, tfsCurrState, tfsBcState, tfsListenState,
      tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen in *;
    (eapply bisim_del_pres; [del_self_tac | eassumption | eassumption]).
Qed.
(*Proof: lift delay preservation results in a similar fashion to del_pres_nextSinceState*)

(*** The broadcaster's wait, observed through bisimulation ***)
(** A state predicate is a bisimilarity class, and two named states with different
parameters can fall in one class when the difference is not observable (root cause 10 of the
first proving pass). The broadcaster's wait is not such a case: its timer is observable through
the moment its position read becomes enabled, and its mode through the message it then
broadcasts. The results below make that precise, and say what a wait delays into.*)

(** A waiting broadcaster whose timer has run out reads its position at once.*)
Lemma bcWait_pos_read_zero (m : Mode) (e : Exp) :
  evalExpFunTime e = Some zeroTime ->
  exists q, bcWait m e -PA- chanPos ;? [basePosition origin] -PA> q.
Proof.
  intro E. eexists. unfold bcWait. apply stepDpChoiceL. apply stepDpChoiceR.
  apply stepDpTimeOut; [ | exact E]. apply stepDpIn. typed_vals.
Qed.

(** Only a timer that has run out lets a waiting broadcaster read its position.*)
Lemma bcWait_pos_read_inv (m : Mode) (e : Exp) (v : list BaseValue) q :
  bcWait m e -PA- chanPos ;? v -PA> q -> evalExpFunTime e = Some zeroTime.
Proof.
  unfold bcWait. intro S. invert_disc_prefixes. assumption.
Qed.

(** What a waiting broadcaster delays into: a wait whose timer has counted down, when the
timer is well formed and at least the delay; a wait that reads its position at once, when the
timer ran out during the delay; and itself, when the timer is ill formed.*)
Lemma bcWait_del_cases (m : Mode) (e : Exp) (d : Delay) q :
  bcWait m e -PD- d -PD> q ->
  (exists (t : Time) (H : d <= t), evalExpFunTime e = Some t /\ q = bcWait m (minusTime t d H)) \/
  (exists t, evalExpFunTime e = Some t /\ nonneg (time t) < pos (delay d) /\
    exists q', q -PA- chanPos ;? [basePosition origin] -PA> q') \/
  (evalExpFunTime e = None /\ q = bcWait m e).
Proof.
  unfold bcWait. intro D. invert_del_prefixes.
  - right. left. eexists. split; [eassumption | ]. split.
    + match goal with [ |- _ < pos (delay (_ +dt+ ?d0)) ] =>
        pose proof (cond_pos (delay d0)) end. simpl. lra.
    + eexists. apply stepDpChoiceL. apply stepDpChoiceR. apply stepDpIn. typed_vals.
  - left. do 2 eexists. split; [eassumption | reflexivity].
  - right. right. split; [assumption | reflexivity].
Qed.

(** A waiting broadcaster with a well-formed timer reads its position at once if the timer is
zero, and after delaying by the timer otherwise.*)
Lemma bcWait_pos_read (m : Mode) (t : Time) :
  (nonneg (time t) = 0 /\ exists q, bcWait m t -PA- chanPos ;? [basePosition origin] -PA> q) \/
  (exists (d : Delay) q, nonneg (time t) = pos (delay d) /\ bcWait m t -PD- d -PD> q /\
   exists q', q -PA- chanPos ;? [basePosition origin] -PA> q').
Proof.
  destruct t as [[r nn]]. destruct (Rle_lt_or_eq_dec 0 r nn) as [Hlt | Heq].
  - right. set (d := mkDelay (mkposreal r Hlt)).
    exists d (bcWait m (minusTime r d (Rle_refl r))). split; [reflexivity | ]. split.
    + unfold bcWait. apply stepTpSum; [apply stepTpSum | apply stepTpIn]; [apply stepTpIn | ].
      eapply (stepTpDelSub _ d _ (mkTime (mknonnegreal r nn)) (Rle_refl r)). reflexivity.
    + apply bcWait_pos_read_zero. unfold liftTimeExp. rewrite evalExpFunTime_time.
      f_equal. apply timeEqR. simpl. ring.
  - left. split; [simpl; symmetry; exact Heq | ].
    apply bcWait_pos_read_zero. unfold liftTimeExp. rewrite evalExpFunTime_time.
    f_equal. apply timeEqR. simpl. symmetry. exact Heq.
Qed.

(* begin helpers for sleeping_not_bcWait *)
(** The sleeping process can never input on the position channel, so it is not bisimilar to
any process that can.*)
Local Lemma sleeping_pos_in_not q q' v :
  sleeping ~p~ q -> q -PA- chanPos ;? v -PA> q' -> False.
Proof.
  intros S T. destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ S) T) as [p' [Sp _]].
  unfold sleeping in Sp. invert_disc_prefixes.
Qed.

(** The sleeping process delays only to itself.*)
Local Lemma del_self_sleeping d s : sleeping -PD- d -PD> s -> s = sleeping.
Proof. revert d s. unfold sleeping. del_self_tac. Qed.
(* end helpers *)

(** The sleeping process is not bisimilar to any wait: a wait can, possibly after a delay, input
on the position channel.*)
Lemma sleeping_not_bcWait (m : Mode) (x : Time) : sleeping ~p~ bcWait m x -> False.
Proof.
  intro B. destruct (bcWait_pos_read m x) as [[_ [q S]] | [d [q [_ [TD [q' S]]]]]].
  - eapply sleeping_pos_in_not; [exact B | exact S].
  - destruct (bisim_step_del _ _ _ _ (bisim_symm _ _ B) TD) as [s [TS BS]].
    apply del_self_sleeping in TS. subst s.
    eapply sleeping_pos_in_not; [apply bisim_symm; exact BS | exact S].
Qed.

(* begin helpers for bcWait_bisim_inj *)
(** Of two bisimilar waits, neither has the shorter timer: when the shorter one has run out,
that side reads its position and the other cannot.*)
Local Lemma bcWait_bisim_timer_le (m1 m2 : Mode) (t1 t2 : Time) :
  bcWait m1 t1 ~p~ bcWait m2 t2 -> t2 <= t1.
Proof.
  intro B. destruct (Rle_or_lt t2 t1) as [LE | LT]; [exact LE | exfalso].
  destruct (bcWait_pos_read m1 t1) as [[Z [q S]] | [d [q [EQ [TD [q' S]]]]]].
  - (* t1 is zero: the other wait reads its position now, so its timer is zero too *)
    destruct (bisim_disc_match _ _ _ _ B S) as [r R].
    apply bcWait_pos_read_inv in R. apply evalExpFunTime_zero_inv in R. simpl in *. lra.
  - (* after delaying by t1, the other wait reads its position, so its timer was t1 *)
    destruct (bisim_step_del _ _ _ _ B TD) as [q2 [TD2 BQ]].
    destruct (bisim_disc_match _ _ _ _ BQ S) as [r R].
    destruct (bcWait_del_cases _ _ _ _ TD2) as [[t [H [E EQ2]]] | [[t [E [LTd _]]] | [E _]]].
    + subst q2. apply bcWait_pos_read_inv in R. apply evalExpFunTime_zero_inv in R.
      unfold liftTimeExp in E. rewrite evalExpFunTime_time in E. injection E as E. subst t.
      simpl in *. lra.
    + unfold liftTimeExp in E. rewrite evalExpFunTime_time in E. injection E as E. subst t.
      simpl in *. lra.
    + unfold liftTimeExp in E. rewrite evalExpFunTime_time in E. discriminate.
Qed.

(** Two bisimilar waits whose timers have run out are for the same mode: each reads its
position and then offers its mode on outProc, and the other has to match.*)
Local Lemma bcWait_bisim_mode_zero (m1 m2 : Mode) (e1 e2 : Exp) :
  evalExpFunTime e1 = Some zeroTime -> evalExpFunTime e2 = Some zeroTime ->
  bcWait m1 e1 ~p~ bcWait m2 e2 -> m1 = m2.
Proof.
  intros E1 E2 B.
  destruct (bcWait_pos_read_zero m1 e1 E1) as [q1 S1].
  destruct (bisim_step_disc _ _ _ _ B S1) as [q2 [S2 BQ]].
  unfold bcWait in S1, S2. invert_disc_prefixes. clean_proc_hyp BQ.
  bt_step BQ (chanOutProc ;! [baseMode m1, basePosition origin]) S3.
  destruct (bisim_step_disc _ _ _ _ BQ S3) as [r2 [R2 _]].
  invert_app_trans. invert_disc_prefixes. output_values. reflexivity.
Qed.
(* end helpers *)

(** Bisimilar waits have the same mode and the same timer.*)
Lemma bcWait_bisim_inj (m1 m2 : Mode) (t1 t2 : Time) :
  bcWait m1 t1 ~p~ bcWait m2 t2 -> m1 = m2 /\ t1 = t2.
Proof.
  intro B.
  assert (EQ : t1 = t2).
  { apply timeEqR. apply Rle_antisym.
    - exact (bcWait_bisim_timer_le _ _ _ _ (bisim_symm _ _ B)).
    - exact (bcWait_bisim_timer_le _ _ _ _ B). }
  subst t2. split; [ | reflexivity].
  destruct (bcWait_pos_read m1 t1) as [[Z _] | [d [q [EQ [TD _]]]]].
  - (* the timers are zero already *)
    eapply bcWait_bisim_mode_zero; [ | | exact B]; unfold liftTimeExp;
      rewrite evalExpFunTime_time; f_equal; apply timeEqR; simpl; exact Z.
  - (* run the timers out first *)
    destruct (bisim_step_del _ _ _ _ B TD) as [q2 [TD2 BQ]].
    destruct (bcWait_del_cases _ _ _ _ TD) as [[t [H [E E1]]] | [[t [E [LTd _]]] | [E _]]];
      destruct (bcWait_del_cases _ _ _ _ TD2) as [[t' [H' [E' E2]]] | [[t' [E' [LTd' _]]] | [E' _]]];
      unfold liftTimeExp in E, E'; rewrite evalExpFunTime_time in E, E';
      try discriminate; injection E as E; injection E' as E'; subst t t'; simpl in *; try lra.
    subst q q2. eapply bcWait_bisim_mode_zero; [ | | exact BQ]; unfold liftTimeExp;
      rewrite evalExpFunTime_time; f_equal; apply timeEqR; simpl; lra.
Qed.

(*** Backward delay tracking ***)

(** Every overlap state but ovWait delays only to itself, and ovWait delays to an ovWait. So
an overlap component that delays into a state Z that no ovWait is bisimilar to was in Z
before the delay.*)
Lemma overlap_del_bkwd (Z p p' : ProcTerm) (d : Delay) :
  overlapState p -> p -PD- d -PD> p' -> p' ~p~ Z ->
  (forall m e2 e3 e4, ovWait m e2 e3 e4 ~p~ Z -> False) -> p ~p~ Z.
Proof.
  intros OS D BZ NW.
  destruct (overlapState_shape _ OS)
    as [B | m B | m e2 e3 e4 B | m e2 l B | m B | B | B | B | B | m B | B | B | B];
    try solve [eapply bisim_trans; [exact B | ]; eapply bisim_trans; [ | exact BZ];
      apply bisim_symm; eapply bisim_del_pres; [del_self_body | exact B | exact D]].
  exfalso. destruct (bisim_step_del _ _ _ _ B D) as [q [TQ BQ]].
  destruct (ovWait_del_shape _ _ _ _ _ _ TQ) as [e3' [e4' B']].
  eapply NW. eapply bisim_trans; [apply bisim_symm; exact B' | ].
  eapply bisim_trans; [apply bisim_symm; exact BQ | exact BZ].
Qed.

(** No process is both ovReady and ovWait.*)
Lemma ovReady_ovWait_bisim_not (m1 m2 : Mode) u1 (l : Position) u2 x2 y2 :
  ovWait m2 u2 x2 y2 ~p~ ovReady m1 u1 l -> False.
Proof. intro B. ovWait_bisim_contra B. Qed.

(** Two bisimilar ovWait, the second with a well-formed position timer, stay bisimilar with the
same timers in both.*)
Local Lemma ovWait_bisim_same_timers (m1 m2 : Mode) u1 x1 y1 u2 x2 y2 t e3 e4 :
  ovWait m1 u1 x1 y1 ~p~ ovWait m2 u2 x2 y2 -> evalExpFunTime y2 = Some t ->
  ovWait m1 u1 e3 e4 ~p~ ovWait m2 u2 e3 e4.
Proof.
  intros B E.
  assert (EM : m2 = m1)
    by exact (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _ E (bisim_symm _ _ B))).
  subst m2.
  destruct (ovWait_bisim_pos_timeout _ _ _ _ _ _ _ _ _ B E) as [x1' [y1' [x2' [y2' [B' E']]]]].
  clear B E. unfold ovWait in B' |- *.
  apply choice_bisim_context; [ | apply bisim_refl].
  apply choice_bisim_context; [apply bisim_refl | ].
  apply del_bisim_context. apply inPrefix_bisim_context. intros v TV.
  match goal with [ |- ?L ~p~ ?R ] =>
    assert (S : (( chanAbort ? ovAbortN $+$ chanBad ? tfsStartN) $+$
      $< y2' >$ chanPos $< vL >$ ? ovReadyN $( [eBase (baseMode m1), u2, eVar vL] )$) $+$
      $< x2' >$ chanPause ! switchBcN $( eBase (baseMode m1) )$ -PA- chanPos ;? v -PA> R) end.
  { apply stepDpChoiceL. apply stepDpChoiceR. apply stepDpTimeOut; [ | exact E'].
    apply stepDpIn. exact TV. }
  destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ B') S) as [r [R BR]].
  invert_disc_prefixes. apply bisim_symm. exact BR.
Qed.

(** A timer that is below exactly the delays d + d' with d' above t, and is not below d,
is t + d.*)
Local Lemma timer_shift (e : Exp) (d : Delay) (t : Time) :
  (forall d' : Delay, (exists t1, evalExpFunTime e = Some t1 /\
    nonneg (time t1) < pos (delay (d +d+ d'))) <-> nonneg (time t) < pos (delay d')) ->
  ~ (exists t1, evalExpFunTime e = Some t1 /\ nonneg (time t1) < pos (delay d)) ->
  evalExpFunTime e = Some (delToTime (t +dt+ d)).
Proof.
  intros H N. apply timer_from_delays. intro d''.
  destruct (Rlt_le_dec (pos (delay d)) (pos (delay d''))) as [GT | LE].
  - assert (EQ : d'' = d +d+ minusDelay d'' d GT)
      by (rewrite addDelayComm; symmetry; apply minusAddDelay).
    rewrite EQ. rewrite (H (minusDelay d'' d GT)). simpl. lra.
  - split.
    + intros [t1 [E1 L1]]. exfalso. apply N. exists t1. split; [exact E1 | lra].
    + intro L. exfalso. simpl in L. pose proof (cond_nonneg (time t)). lra.
Qed.

(** Back across a delay d into ovWait m t x y, an overlap component could read its position
during the delay, or was ovWait for m with first parameter t, a time as its pause timer and
y + d as its position timer; its pause timer was x + d unless it could pause during the
delay.*)
Lemma ovWait_timers_del_bkwd (p p' : ProcTerm) (d : Delay) (m : Mode) (t x y : Time) :
  overlapState p -> p -PD- d -PD> p' -> ovWaitState m t x y p' ->
  sort (chanPos ;? [basePosition origin]) d p \/
  exists (x0 : Time), ovWaitState m t x0 (delToTime (y +dt+ d)) p /\
    (~ sort (chanPause *!) d p -> x0 = delToTime (x +dt+ d)).
Proof.
  intros OS D OW. red in OW.
  destruct (overlapState_shape _ OS)
    as [B | m0 B | m0 e2 e3 e4 B | m0 e2 l B | m0 B | B | B | B | B | m0 B | B | B | B];
    try solve [exfalso; match type of B with _ ~p~ ?Z =>
      assert (C : ovWait m t x y ~p~ Z) by (eapply bisim_trans;
        [apply bisim_symm; exact OW | eapply bisim_del_pres; [del_self_body | exact B | exact D]])
      end; first [ovWait_bisim_contra C | destruct (dormant_mNext_in _ m C) as [q S];
        unfold ovWait in S; invert_disc_prefixes]].
  destruct (bisim_step_del _ _ _ _ B D) as [a' [DA BA]].
  destruct (ovWait_del_shape _ _ _ _ _ _ DA) as [e3' [e4' BS]].
  assert (BW : ovWait m0 e2 e3' e4' ~p~ ovWait m t x y) by (eapply bisim_trans;
    [apply bisim_symm; exact BS | eapply bisim_trans; [apply bisim_symm; exact BA | exact OW]]).
  assert (EM : m = m0) by exact (proj1 (ovWait_bisim_mode _ _ _ _ _ _ _ _ _
    (evalExpFunTime_time y) (bisim_symm _ _ BW))).
  subst m0.
  pose proof (bisim_del_any _ _ B (ovWait_del_any _ _ _ _)) as PD.
  pose proof (bisim_del_any _ _ OW (ovWait_del_any _ _ _ _)) as PD'.
  assert (HY : forall d' : Delay, (exists t4, evalExpFunTime e4 = Some t4 /\
    nonneg (time t4) < pos (delay (d +d+ d'))) <-> nonneg (time y) < pos (delay d')).
  { intro d'. rewrite <- (ovWait_sort_pos m e2 e3 e4 origin).
    rewrite <- (bisim_sort_iff _ _ _ _ B (PD _)). rewrite <- (sortDerivEquiv _ _ _ _ _ D).
    rewrite (bisim_sort_iff _ _ _ _ OW (PD' _)). rewrite ovWait_sort_pos.
    unfold liftTimeExp. rewrite evalExpFunTime_time. split.
    - intros [t1 [E1 L1]]. injection E1 as E1. subst. exact L1.
    - intro L. exists y. split; [reflexivity | exact L]. }
  assert (HX : forall d' : Delay, (exists t3, evalExpFunTime e3 = Some t3 /\
    nonneg (time t3) < pos (delay (d +d+ d'))) <-> nonneg (time x) < pos (delay d')).
  { intro d'. rewrite <- (ovWait_sort_pause m e2 e3 e4).
    rewrite <- (bisim_sort_iff _ _ _ _ B (PD _)). rewrite <- (sortDerivEquiv _ _ _ _ _ D).
    rewrite (bisim_sort_iff _ _ _ _ OW (PD' _)). rewrite ovWait_sort_pause.
    unfold liftTimeExp. rewrite evalExpFunTime_time. split.
    - intros [t1 [E1 L1]]. injection E1 as E1. subst. exact L1.
    - intro L. exists x. split; [reflexivity | exact L]. }
  destruct (Classical_Prop.classic (sort (chanPos ;? [basePosition origin]) d p)) as [SP | NSP];
    [left; exact SP | right].
  assert (E4 : evalExpFunTime e4 = Some (delToTime (y +dt+ d))).
  { apply timer_shift; [exact HY | ]. intro C. apply NSP.
    apply (bisim_sort_iff _ _ _ _ B (PD _)). apply ovWait_sort_pos. exact C. }
  destruct (proj2 (HX (x +dt+ mkDelay onePos))) as [t3 [E3 _]];
    [simpl; pose proof (cond_pos onePos); lra | ].
  exists t3. split.
  - red. eapply bisim_trans; [exact B | ].
    eapply bisim_trans; [ | exact (ovWait_bisim_same_timers _ _ _ _ _ _ _ _ _ _ _ BW
      (evalExpFunTime_time y))].
    unfold ovWait. repeat apply choice_bisim_context; try apply bisim_refl;
      apply del_bisim_guard; unfold liftTimeExp; rewrite evalExpFunTime_time; assumption.
  - intro NSX. assert (E3' : evalExpFunTime e3 = Some (delToTime (x +dt+ d))).
    { apply timer_shift; [exact HX | ]. intro C. apply NSX.
      apply (bisim_sort_iff _ _ _ _ B (PD _)). apply ovWait_sort_pause. exact C. }
    rewrite E3 in E3'. injection E3' as E3'. exact E3'.
Qed.

(** A wait with a well-formed position timer delays into a wait for the same mode, with a time as
its position timer.*)
Lemma ovWait_del_posTimer (m : Mode) (u x y : Exp) (t : Time) (d : Delay) q :
  evalExpFunTime y = Some t -> ovWait m u x y -PD- d -PD> q ->
  exists (x' : Exp) (t' : Time), q ~p~ ovWait m u x' t'.
Proof.
  unfold ovWait. intros E D. invert_del_prefixes; try congruence;
    do 2 eexists; del_timers_bisim.
Qed.

(** init shows its mode: after reading the current mode it waits with its position timer run
out, so ovWait_bisim_mode_zero applies.*)
Lemma init_bisim_mode (m1 m2 : Mode) : init m1 ~p~ init m2 -> m1 = m2.
Proof.
  intro B.
  eassert (S1 : init m1 -PA- chanMCurrRead ;? [baseMode m1] -PA> _)
    by (unfold init; step_search).
  destruct (bisim_step_disc _ _ _ _ B S1) as [q2 [S2 BQ]].
  unfold init in S1, S2. invert_disc_prefixes. clean_proc_hyp BQ.
  bt_step BQ (chanPos ;? [basePosition origin]) S3.
  destruct (bisim_step_disc _ _ _ _ BQ S3) as [r [R BR]].
  invert_app_trans. invert_disc_prefixes. clean_proc_hyp BR.
  match type of BR with app _ (eBase ?b :: _) ~p~ _ =>
    bt_step BR (chanOutProc ;! [b, basePosition origin]) S4 end.
  destruct (bisim_step_disc _ _ _ _ BR S4) as [r4 [R4 _]].
  invert_app_trans. invert_disc_prefixes. output_values. reflexivity.
Qed.

(** tfsStart and init both read the current mode first, and then differ.*)
Lemma tfsStart_not_init (m : Mode) : tfsStart ~p~ init m -> False.
Proof.
  intro B.
  eassert (S1 : tfsStart -PA- chanMCurrRead ;? [baseMode m] -PA> _)
    by (unfold tfsStart; step_search).
  destruct (bisim_step_disc _ _ _ _ B S1) as [q2 [S2 BQ]].
  unfold tfsStart, init in S1, S2. invert_disc_prefixes. clean_proc_hyp BQ.
  unfold_app_hyp BQ. unfold_app_hyp_l BQ. refute_by_chan BQ.
Qed.

(** After a step into init m, the overlap component was dormant and read m on mNext.*)
Lemma init_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) :
  p -PA- a -PA> p' -> overlapState p -> p' ~p~ init m ->
  p ~p~ dormant /\ a = chanMNextRead ;? [baseMode m].
Proof.
  intros TR O SP. backtrack_shape SP.
  - (* dormant read a mode m0 on mNext, into init m0 *)
    change (init m0 ~p~ init m) in BT. apply init_bisim_mode in BT. subst m0.
    split; [exact B | reflexivity].
  - exfalso. apply (tfsStart_not_init m). exact BT.
  - exfalso. apply (tfsStart_not_init m). exact BT.
Qed.

(** After a step into ovWait, whatever its timers, the overlap component was init or ovReady for
the same mode, and the position timer is well formed: init sets it to zero and ovReady to the
period.*)
Lemma ovWaitExp_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) (e2 e3 e4 : Exp) :
  p -PA- a -PA> p' -> overlapState p -> p' ~p~ ovWait m e2 e3 e4 ->
  (exists t, evalExpFunTime e4 = Some t) /\
  (p ~p~ init m \/ exists (u : Exp) (l : Position), p ~p~ ovReady m u l).
Proof.
  intros TR O SP. backtrack_shape SP.
  - (* init m0: its derivative's position timer is zero *)
    apply ovWait_bisim_mode with (t1 := zeroTime) in BT; [ | reflexivity].
    destruct BT as [EQ E4]. subst m0. split; [exact E4 | left; exact B].
  - (* ovReady m0 u l: its derivative's position timer is the period *)
    apply ovWait_bisim_mode with (t1 := period m0) in BT; [ | apply evalExpFunTime_period].
    destruct BT as [EQ E4]. subst m0. split; [exact E4 | right; do 2 eexists; exact B].
Qed.

(** After a step into ovReady, whatever its timer, the overlap component was ovWait for the same
mode.*)
Lemma ovReadyExp_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) (u : Exp) (l : Position) :
  p -PA- a -PA> p' -> overlapState p -> p' ~p~ ovReady m u l ->
  exists e2 e3 e4, p ~p~ ovWait m e2 e3 e4.
Proof.
  intros TR O SP. backtrack_shape SP.
  match type of BT with outPrefix _ (eBase ?b1 :: eBase ?b :: nil) _ ~p~ _ =>
    bt_step BT (chanOutProc ;! [b1, b]) S2 end.
  destruct (bisim_step_disc _ _ _ _ BT S2) as [r2 [R2 _]].
  invert_disc_prefixes. output_values.
  do 3 eexists. exact B.
Qed.

(** Before a delay into ovWait m, the overlap component was an ovWait, which was for m if its
position timer was well formed: every other overlap state delays only to itself.*)
Lemma ovWait_del_bkwd (p p' : ProcTerm) (d : Delay) (m : Mode) (e2 e3 e4 : Exp) :
  overlapState p -> p -PD- d -PD> p' -> p' ~p~ ovWait m e2 e3 e4 ->
  exists (m0 : Mode) (f2 f3 f4 : Exp), p ~p~ ovWait m0 f2 f3 f4 /\
    ((exists t, evalExpFunTime f4 = Some t) -> m0 = m /\ exists t, evalExpFunTime e4 = Some t).
Proof.
  intros OS D BZ.
  destruct (overlapState_shape _ OS)
    as [B | m0 B | m0 f2 f3 f4 B | m0 f2 l B | m0 B | B | B | B | B | m0 B | B | B | B];
    try solve [exfalso; match type of B with p ~p~ ?X =>
      assert (B' : p' ~p~ X) by (eapply bisim_del_pres; [del_self_body | exact B | exact D]);
      pose proof (bisim_trans _ _ _ (bisim_symm _ _ BZ) B') as BT;
      unfold dormant, init, tfsStart in BT; try unfold liftVarList in BT;
      ovWait_bisim_contra BT end].
  exists m0 f2 f3 f4. split; [exact B | ]. intros [t4 E4].
  destruct (bisim_step_del _ _ _ _ B D) as [q [TQ BQ]].
  destruct (ovWait_del_posTimer _ _ _ _ _ _ _ E4 TQ) as [x' [t' B']].
  eapply ovWait_bisim_mode with (t1 := t'); [apply evalExpFunTime_time | ].
  eapply bisim_trans; [apply bisim_symm; exact B' | ].
  eapply bisim_trans; [apply bisim_symm; exact BQ | exact BZ].
Qed.

(****************** Linking ******************)
(** The protocol's software is a triple of components. The language's results about the
n-ary composition parAll apply to it once the triple is written as parAll p1 [p2, p3], and
one tactic, triple_pos, turns the positions those results speak of back into the three
components. The tactics after it rebuild the triple-shaped facts the proofs below use.*)

(** Inverts a discrete step H of a triple into its cases: one component steps, or two
synchronise.*)
Ltac triple_disc_inv H :=
  triple_parAll H; apply parAll_disc_inv in H;
  destruct H as [? [? [? [[? H] | [? [? [? [? [? [? [? [H ?]]]]]]]]]]]]; triple_pos.

(* begin helpers for link_reach_triple_tau *)
Lemma link_reach_triple_tau_bc p p' :
  broadcastState p -> p -PA- tauAct -PA> p' -> False.
Proof.
  intros S T. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra.
Qed.

Lemma link_reach_triple_tau_ov p p' :
  overlapState p -> p -PA- tauAct -PA> p' -> False.
Proof.
  intros S T. destruct (overlapState_shape _ S); prot_outProc_in_not_contra.
Qed.

Lemma link_reach_triple_tau_ls p p' :
  listenerState p -> p -PA- tauAct -PA> p' -> False.
Proof.
  intros S T. destruct (listenerState_shape _ S); prot_outProc_in_not_contra.
Qed.

(* end helpers *)

Lemma link_reach_triple_tau (p1 p2 p3 p1' p2' p3' : ProcTerm) :
  p1 $||$ p2 $||$ p3 -PA- tauAct -PA> p1' $||$ p2' $||$ p3' ->
  protocolState (p1 $||$ p2 $||$ p3) -> exists c v,
  (p1 -PA- c ;! v -PA> p1' /\ p2 -PA- c ;? v -PA> p2' /\ p3 = p3') \/
  (p1 -PA- c ;? v -PA> p1' /\ p2 -PA- c ;! v -PA> p2' /\ p3 = p3') \/
  (p1 -PA- c ;! v -PA> p1' /\ p3 -PA- c ;? v -PA> p3' /\ p2 = p2') \/
  (p1 -PA- c ;? v -PA> p1' /\ p3 -PA- c ;! v -PA> p3' /\ p2 = p2') \/
  (p2 -PA- c ;! v -PA> p2' /\ p3 -PA- c ;? v -PA> p3' /\ p1 = p1') \/
  (p2 -PA- c ;? v -PA> p2' /\ p3 -PA- c ;! v -PA> p3' /\ p1 = p1').
Proof.
  intros T P. inversion P as [? ? ? BS OS LS]; subst.
  triple_disc_inv T;
    try match goal with [K : p1 -PA- tauAct -PA> _ |- _] =>
      destruct (link_reach_triple_tau_bc _ _ BS K) end;
    try match goal with [K : p2 -PA- tauAct -PA> _ |- _] =>
      destruct (link_reach_triple_tau_ov _ _ OS K) end;
    try match goal with [K : p3 -PA- tauAct -PA> _ |- _] =>
      destruct (link_reach_triple_tau_ls _ _ LS K) end;
    do 2 eexists; eauto 9.
Qed.
(**Prove more general result including taus and then eliminate the taus by anti-activation
  on each broadcast, listener and overlap process?
  Proof: From reachable, we have that p1, p2, p3 are braodcast, overlap, listener
  protocol components respectively. We then invert on the tau action and eliminate the tau
  cases for pi -tau-> pi' as they come up because none of the protocol components can ever
  do a tau (show this elsewhere). Leaving us our goal.*)

(** Only the overlap component switches mode.*)
Lemma broadcast_mCurr_out_not p p' v :
  broadcastState p -> p -PA- chanMCurrWrite ;! v -PA> p' -> False.
Proof. intros S T. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra. Qed.

Lemma listener_mCurr_out_not p p' v :
  listenerState p -> p -PA- chanMCurrWrite ;! v -PA> p' -> False.
Proof. intros S T. destruct (listenerState_shape _ S); prot_outProc_in_not_contra. Qed.

(** The broadcaster outputs only on outProc.*)
Lemma broadcast_out_outProc p p' c v :
  broadcastState p -> p -PA- c ;! v -PA> p' -> c = chanOutProc.
Proof.
  intros S T. destruct (broadcastState_shape _ S) as [B | m e B | m l B];
    try prot_outProc_in_not_contra.
  destruct (bisim_disc_match _ _ _ _ B T) as [q R]. unfold bcReady in R.
  invert_disc_prefixes. reflexivity.
Qed.

(****************** Reachability Results ******************)
(**In here we put results that are specific to reachable processes,
i.e. ones that can be reached by the transition semantics via the
protocol process. Results about the relationship between states of
the various components belong here e.g. "If the overlap component
is in such a state, then the listener is paused".*)

(** reachableProt is the language's reachability from the protocol process.*)
Lemma reachableProt_reachableFrom (p : ProcTerm) :
  reachableProt p <-> reachableFrom procProtocol p.
Proof.
  split; intro R; induction R;
    eauto using reachprBase, reachprDisc, reachprDel,
      reachableFromBase, reachableFromDisc, reachableFromDel.
Qed.

(**If p is reachable from the "protocol" process via
the semantics, then it has the "shape" of a protocol process.*)
Theorem reachableProt_triple (p : ProcTerm) : 
  reachableProt p -> protocolState p.
Proof.
  intro R. apply reachableProt_reachableFrom in R.
  change procProtocol with (parAll sleeping [dormant, listening]) in R.
  apply reachableFrom_parAll in R. destruct R as [p1 [ps [E F]]]. positions_inv. subst.
  constructor; assumption.
Qed.
(**Proof: The components of a parallel composition each stay reachable from where they
started (reachableFrom_parAll), and reachable from the initial component is what each
component-state predicate says.*)

(** A reachable protocol process uses its entity's channels correctly.*)
Lemma reachableProt_correctChannelUsage (p : ProcTerm) :
  reachableProt p -> correctChannelUsage p.
Proof.
  intro R. apply reachableProt_reachableFrom in R.
  exact (oneWayUsage_reachableFrom _ _ _ _ protocol_correctChannelUsage R).
Qed.

(****************** Brute Force ******************)
(*I think these can be solved by inversion on the complex state predicate
followed by activation or anti-activation. Or could be followed by some
sort of tracking tactic e.g. gotMsg_state.*)

Theorem bc_outProc_out (p p' : ProcTerm) (m : Mode) (l : Position) : 
  p -PA- chanOutProc ;! [baseMode m, basePosition l] -PA> p' -> broadcastState p ->
  bcReadyState m l p /\ bcWaitState m (period m) p'.
Proof.
  intros T B. destruct (broadcastState_shape _ B) as [S | v e S | v1 v2 S];
    try solve [prot_outProc_in_not_contra].
  destruct (bisim_step_disc _ _ _ _ S T) as [q [TQ BQ]]. unfold bcReady in TQ.
  invert_disc_prefixes.
  repeat match goal with [H : evalExpLists (_ :: _) _ |- _] => inversion H; subst; clear H end.
  repeat match goal with [H : evalExp (eBase _) _ |- _] => inversion H; subst; clear H end.
  split; [assumption | ]. red. eapply bisim_trans; [exact BQ | ].
  eapply bisim_trans; [apply app_bisim_def; reflexivity | ].
  unfold bcWait. simpl. clean_proc.
  apply choice_bisim_context; [ | apply bisim_refl].
  apply choice_bisim_context; [apply bisim_refl | ].
  apply del_bisim_guard. unfold evalExpFunTime; simpl; destruct (period m); reflexivity.
Qed.
(**Proof: Brute force try all the other possible broadcast states (auto tactic) and this is the only one that matches*)

(** Only ovReady outputs on outProc. Its timer is a computed expression, which may be ill
formed when the mode read on mCurr was not a mode, so the lemma leaves it as an expression
rather than a time.*)
Theorem ovlp_outProc_out (p p' : ProcTerm) (m : Mode) (l : Position) : 
  p -PA- chanOutProc ;! [baseMode m, basePosition l] -PA> p' -> overlapState p ->
  exists t, ovReadyStateExp m t l p /\
  ovWaitStateExp m (t (-) ePeriod m) (t (-) ePeriod m) (ePeriod m) p'.
Proof.
  intros T O. destruct (overlapState_shape _ O)
    as [S | v S | v e2 e3 e4 S SC | v1 e2 v3 S | m0 S | S | S | S | S | v S | S | S | S];
    try solve [prot_outProc_in_not_contra].
  destruct (bisim_step_disc _ _ _ _ S T) as [q [TQ BQ]]. unfold ovReady in TQ.
  invert_disc_prefixes.
  repeat match goal with [H : evalExpLists (_ :: _) _ |- _] => inversion H; subst; clear H end.
  repeat match goal with [H : evalExp (eBase _) _ |- _] => inversion H; subst; clear H end.
  exists e2. split; [exact S | ]. red.
  eapply bisim_trans; [exact BQ | ]. unfold_app_bisim. apply bisim_refl.
Qed.
(**Proof: Brute force. Analogous to bc_outProc_out but with overlap states*)

Theorem bc_mCurr_out_not (p p' : ProcTerm) : 
  p -PA- chanMCurrWrite ;! [] -PA> p' -> broadcastState p -> False.
Proof.
  intros TR S. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra.
Qed.
(**Proof: Brute force analysis of all broadcast states and none of them are enabled on this action*)

Theorem bc_abort_in_not (p p' : ProcTerm) : 
  p -PA- chanAbort*? -PA> p' -> broadcastState p -> False.
Proof.
  intros TR S. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra.
Qed.
(**Proof: Brute force analysis of all broadcast states and none of them are enabled on this action*)

Theorem listen_mCurr_out_not (p p' : ProcTerm) : 
  p -PA- chanMCurrWrite ;! [] -PA> p' -> listenerState p -> False.
Proof.
  intros TR S. destruct (listenerState_shape _ S); prot_outProc_in_not_contra.
Qed.
(**Proof: Brute force analysis of all listener states and none of them are enabled on this action*)

(**The two cases where the overlap component can output on mCurr.*)
Theorem ovlp_mCurr_out (p p' : ProcTerm) : 
  p -PA- chanMCurrWrite ;! [] -PA> p' -> overlapState p ->
  (switchCurrState p /\ switchListenState p') \/
  (tfsCurrState p /\ tfsBcState p').
Proof.
  intros TR S. destruct (overlapState_shape _ S)
    as [B | v B | v e2 e3 e4 B SC | v1 e2 v3 B | m0 B | B | B | B | B | v B | B | B | B];
    try solve [prot_outProc_in_not_contra];
    destruct (bisim_step_disc _ _ _ _ B TR) as [q [TQ BQ]];
    [unfold switchCurr in TQ | unfold tfsCurr in TQ]; invert_disc_prefixes;
    [left | right]; (split; [exact B | ]); red;
    (eapply bisim_trans; [exact BQ | ]); apply app_bisim_nil; reflexivity.
Qed.
(**Proof: Brute force analysis on overlap states and show that these are the only two matches*)

Theorem listen_mStable_out_not (p p' : ProcTerm) :
  p -PA- chanMStableWrite ;! [] -PA> p' -> listenerState p -> False.
Proof.
  intros TR S. destruct (listenerState_shape _ S); prot_outProc_in_not_contra.
Qed.

(**The two cases where the overlap component can output on mCurr.*)
Theorem ovlp_abort_in (p p' : ProcTerm) (m : Mode) :
  p -PA- chanAbort*? -PA> p' -> overlapState p ->
  (dormantState p /\ dormantState p') \/
  ovAbortState p' \/
  (tfsCurrState p /\ tfsCurrState p') \/
  (tfsListenState p /\ tfsListenState p').
Proof.
  intros TR OS. destruct (overlapState_shape _ OS)
    as [B | v B | v e2 e3 e4 B SC | v1 e2 v3 B | m0 B | B | B | B | B | v B | B | B | B];
    try solve [prot_outProc_in_not_contra];
    destruct (bisim_step_disc _ _ _ _ B TR) as [q' [TQ BQ]];
    [unfold dormant in TQ | unfold ovWait in TQ | unfold tfsCurr in TQ | unfold tfsListen in TQ];
    invert_disc_prefixes;
    [left; split; [exact B | ] | right; left | right; right; left; split; [exact B | ]
      | right; right; right; split; [exact B | ]];
    red; (eapply bisim_trans; [exact BQ | ]); apply app_bisim_nil; reflexivity.
Qed.
(**Proof: Brute force analysis of overlap states and these are the only ones that fit the transition*)

Theorem bc_mStable_out_not (p p' : ProcTerm) : 
  p -PA- chanMStableWrite*! -PA> p' -> broadcastState p -> False.
Proof.
  intros TR S. destruct (broadcastState_shape _ S); prot_outProc_in_not_contra.
Qed.

(**The two cases where the overlap component can output on mStable: aborting an overlap,
and the self-loop of tfsNext, which keeps its mode.*)
Theorem overlap_mStable_out (p p' : ProcTerm) :
  p -PA- chanMStableWrite*! -PA> p' -> overlapState p ->
  (ovAbortState p /\ dormantState p') \/
  (exists m, tfsNextState m p /\ tfsNextState m p').
Proof.
  intros TR S. destruct (overlapState_shape _ S)
    as [B | v B | v e2 e3 e4 B | v1 e2 v3 B | m0 B | B | B | B | B | v B | B | B | B];
    try solve [prot_outProc_in_not_contra];
    destruct (bisim_step_disc _ _ _ _ B TR) as [q [TQ BQ]];
    [unfold ovAbort in TQ | unfold tfsNext in TQ]; invert_disc_prefixes.
  - left. split; [exact B | ]. red. eapply bisim_trans; [exact BQ | ].
    apply app_bisim_nil; reflexivity.
  - right. exists v. split; [exact B | ]. red. eapply bisim_trans; [exact BQ | ].
    unfold_app_bisim. apply bisim_refl.
Qed.

(*NAME COULD BE CHANGED TO SOMETHING A BIT MORE NORMAL.*)
Lemma gotMsg_state p p' m l : protocolState p ->
  p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p'.
Proof.
  intros PS TR. inversion PS as [p1 p2 p3 BS OS LS]; subst; clear PS.
  inversion TR; subst; clear TR.
  - exfalso. destruct (broadcastState_shape _ BS); prot_outProc_in_not_contra.
  - match goal with [V : p2 $||$ p3 -PA- _ -PA> _ |- _] => inversion V; subst; clear V end.
    + exfalso. destruct (overlapState_shape _ OS); prot_outProc_in_not_contra.
    + constructor.
      destruct (listenerState_shape _ LS) as [H | m0 H | H | m0 H | H | m0 l0 H | m0 e H
        | m0 e H | H | H]; try solve [exfalso; prot_outProc_in_not_contra].
      shape_step_pre B. unfold gotMsgState. shape_body B.
Qed.
(**Proof: p is a protocol process, so can be decomposed into p1 | p2 | p3. Brute force on p1, p2 shows that these don't match. Brute force analysis on listener states shows that the only state that fits for p3 is gotMsgState.*)

(*LOCAL TIDY*)

Lemma ovlp_abort_in_notNextSince p p' :
  p -PA- chanAbort;? [] -PA> p' -> overlapState p -> ~ nextSinceState p'.
Proof.
  intros P O N. destruct (overlapState_shape _ O)
    as [D | v D | v e2 e3 e4 D SC | v1 e2 v3 D | m0 D | D | D | D | D | v D | D | D | D];
    try solve [prot_outProc_in_not_contra];
    destruct (bisim_step_disc _ _ _ _ D P) as [q' [Q B]];
    prot_outProc_in_not_body; invert_disc_prefixes;
    (* The derivative is dormant, ovAbort, tfsCurr or tfsListen. Each acts on a channel no
       nextSince state mentions: mNext, mStable, mCurr or abort, and unpause.*)
    destruct N as [m1 t1 x1 y1 X | m1 t1 l1 X | m1 X | m1 X]; red in X;
    pose proof (bisim_trans _ _ _ (bisim_symm _ _ B) X) as BT; clear B X;
    clean_proc_hyp BT; unfold liftNameProc in BT; unfold_app_hyp_l BT;
    prot_outProc_in_not_body; refute_by_chan BT.
Qed.

End ProtAuxResults.

(** A section's tactics end with it. So that later files can use them, they are declared here.*)

Ltac link_partripdiscex_tac U p1' p2' p3' :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?a -PA> ?p' |- _] =>
  let Q1 := fresh in triple_shape H Q1;
  let U1 := fresh U in decompEx3 Q1 p1' p2' p3' U1
  end.

Ltac link_partripdiscex_tac2 p1' p2' p3' :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?a -PA> ?p' |- _] =>
  let Q1 := fresh in triple_shape H Q1;
  let U1 := fresh in decompEx3 Q1 p1' p2' p3' U1;
  rewrite U1 in H; clear U1
  end.

(** An output of a triple is an output of one component, the other two unchanged; the
three cases become goals, with the facts of each flattened into U names.*)
Ltac link_partripout_tac U :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?c ;! ?v -PA> ?p1' $||$ ?p2' $||$ ?p3' |- _] =>
  let H1 := fresh in
  assert (H1 : p1 -PA- c ;! v -PA> p1' /\ p2 = p2' /\ p3 = p3' \/
    p2 -PA- c ;! v -PA> p2' /\ p1 = p1' /\ p3 = p3' \/
    p3 -PA- c ;! v -PA> p3' /\ p1 = p1' /\ p2 = p2') by
    (triple_disc_nonTau H; eauto 7);
  let H2 := fresh in elimOr3 H1 H2; andflat U
  end.

Ltac link_partripdiscW2_tac H W :=
  match type of H with _ $||$ ?p2 $||$ _ -PA- _ -PA> _ $||$ ?p2' $||$ _ =>
    link_partripdiscW_tac H W (p2 = p2' \/ exists b, p2 -PA- b -PA> p2') end.

Ltac link_partripdiscW3_tac H W :=
  match type of H with _ $||$ _ $||$ ?p3 -PA- _ -PA> _ $||$ _ $||$ ?p3' =>
    link_partripdiscW_tac H W (p3 = p3' \/ exists b, p3 -PA- b -PA> p3') end.

(** The triple is enabled on an action its broadcast, overlap or listener component is
enabled on.*)
Ltac dae_component pos :=
  match goal with [ |- discActEnabled (?p1 $||$ ?p2 $||$ ?p3) _ ] =>
    change (p1 $||$ p2 $||$ p3) with (parAll p1 [p2, p3]);
    eapply parAll_dae_intro; [pos | ] end.

Ltac dae_broadcast := dae_component ltac:(left; reflexivity).

Ltac dae_overlap := dae_component ltac:(right; left; reflexivity).

Ltac dae_listener := dae_component ltac:(right; right; left; reflexivity).

(** The position of a component q among p1, p2 and p3.*)
Ltac triple_index p1 p2 p3 q :=
  lazymatch q with p1 => constr:(0%nat) | p2 => constr:(1%nat) | p3 => constr:(2%nat) end.

(** Closes the goal from a delay DP of a triple, D1 : one component is enabled on an action
and D2 : another is enabled on its complement.*)
Ltac triple_del_sync_not DP D1 D2 :=
  match type of DP with ?p1 $||$ ?p2 $||$ ?p3 -PD- _ -PD> _ =>
  match type of D1 with discActEnabled ?qi _ =>
  match type of D2 with discActEnabled ?qj _ =>
    let i := triple_index p1 p2 p3 qi in let j := triple_index p1 p2 p3 qj in
    exact (parAll_del_sync_not p1 [p2, p3] _ _ i j _ _ _ DP ltac:(discriminate)
      eq_refl eq_refl D1 D2 ltac:(discriminate))
  end end end.

Ltac reachprot U :=
  match goal with
  [H : reachableProt ?p |- _] => let U1 := fresh U in
  lets U1 : reachableProt_triple H
  end.
