(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)


(***************************** Standard Imports *****************************)
  
Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lib.StandardResults.

(***************************** Syntax & Semantics *****************************)

(*The mode transition relation, modeTransRel and the mode transition time,
modeTransTime, have been defined in comhbasics. These will be used for the
init rule, whereby a mode transition is initialised.*)

(** Syntax: a mode state is either a single stable mode, or the transition from one mode
to another, with a certain amount of time remaining until the transition times out and
the mode switch can be finalised.*)
Inductive ModeState : Type :=
  | sing :> Mode -> ModeState
  | transState : Mode -> Mode -> Time -> ModeState.
Notation "<| m , m' , t |>" := (transState m m' t) (at level 30).

(** Coerce a mode state to its current mode.*)
Coercion currModeMState (a : ModeState) : Mode :=
  match a with
  | sing m => m
  | <|m, m', d|> => m
  end. 

(** Strip the next mode off the mode state, if it exists.*)
Definition nextModeMState (a : ModeState) : option Mode :=
  match a with
  | sing m => None
  | <|m, m', d|> => Some m'
  end.

(** Equality on mode states is decidable.*)
Lemma eqDecModeState : eqDec ModeState. unfold eqDec.
  destruct x1, x2; try solve [right; unfold not;
  intros; inversion H]. addHyp (eqDecMode m m0). invertClear H.
  left. subst. reflexivity. right. unfold not. intros.
  apply H0. inversion H. reflexivity.
  addHyp (eqDecMode m m1). invertClear H.
  addHyp (eqDecMode m0 m2). invertClear H.
  addHyp (eqDecTime t t0). invertClear H.
  left. subst. reflexivity. right. unfold not. intros.
  apply H2. inversion H. reflexivity. right. unfold not. intros.
  apply H1. inversion H. reflexivity. right. unfold not. intros.
  apply H0. inversion H. reflexivity. Qed.
 
(** The actions of the mode state are: input/output of a mode on a channel,
or delay.*)
Inductive ActModeState :=
  | amIn : Channel -> Mode -> ActModeState
  | amOut : Channel -> Mode -> ActModeState
  | amOutEmp : Channel -> ActModeState
  | amInEmp : Channel -> ActModeState
  | amDel :> Delay -> ActModeState.

Notation "c .? m" := (amIn c m) (at level 30).
Notation "c .! m" := (amOut c m) (at level 30).
Notation "c @! " := (amOutEmp c) (at level 30).
Notation "c @? " := (amInEmp c) (at level 30).

Reserved Notation "m -ms- a -ms> m'" (at level 75).

(** The semantics of the mode state language.*)
Inductive stepModeState : ModeState -> ActModeState -> ModeState -> Prop :=
  (** A stable mode state can delay arbitrarily and remain unchanged.*)
  | stepMsDelSing : forall (m : Mode) (d : Delay),
    m -ms- d -ms> m
  | stepMsDelTout : forall (m m' : Mode) (d : Delay),
    <| m , m' , zeroTime |> -ms- d -ms> <| m , m' , zeroTime |>
  | stepMsDelGuard : forall (m m' : Mode) (d : Delay) (t t' : Time),
    t = t' +dt+ d -> <| m , m' , t |> -ms- d -ms> <| m , m' , t' |>
  | stepMsTimeout : forall (m m' : Mode) (t : Time) (d : Delay),
    t < d -> <| m , m' , t |> -ms- d -ms> <| m , m' , zeroTime |>
  | stepMsInit : forall (m m' : Mode) (p : m -mtr-> m'),
    m -ms- chanMNextWrite .? m' -ms> <| m , m' , modeTransTime m m' p |>
  | stepMsSwitch : forall (m m' : Mode),
    <| m , m' , zeroTime |> -ms- chanMCurrWrite @? -ms> m'
  | stepMsAbort : forall (m m' : Mode) (t : Time),
    <| m , m' , t |> -ms- chanMStableWrite @? -ms> m
  | stepMsOutCurrSing : forall m : Mode, m -ms- chanMCurrRead .! m -ms> m
  | stepMsOutCurrTrans : forall (m m' : Mode) (t : Time),
    <| m , m' , t |> -ms- chanMCurrRead .! m -ms> <| m , m' , t |>
  | stepMsOutNext : forall (m m' : Mode) (t : Time),
    <| m , m' , t |> -ms- chanMNextRead .! m' -ms> <| m , m' , t |>
  | stepMsOutStable : forall m : Mode, m -ms- chanMStableRead @! -ms> m
  where "m -ms- a -ms> m'" := (stepModeState m a m').

(** A mode state is enabled on a discrete action if it can perform an input of
a mode, an output of a mode or an output of nothing. The discrete action is then
the corresponding input or output as a DiscAct rather than an ActModeState.*)
Inductive discActEnabledMState : DiscAct -> ModeState -> Prop :=
  | daemIn : forall (c : Channel) (m : Mode) (k k' : ModeState),
    k -ms- c .? m -ms> k' -> discActEnabledMState (c ;? [baseMode m]) k
  | daemOutMode : forall (c : Channel) (m : Mode) (k k' : ModeState),
    k -ms- c .! m -ms> k' -> discActEnabledMState (c ;! [baseMode m]) k
  | daemInEmp : forall (c : Channel) (k k' : ModeState),
    k -ms- c @? -ms> k' -> discActEnabledMState (c *?) k
  | daemOutEmp : forall (c : Channel) (k k' : ModeState),
    k -ms- c @! -ms> k' -> discActEnabledMState (c *!) k.

(***************************** Results *****************************)

(** If <m1, m2, t> transitions by d to <m1', m2', t'> then either t' = 0,
or t = t' + d.*)
Lemma delMStateTrans : forall (m1 m2 m1' m2' : Mode) (t t' : Time) (d : Delay),
  <| m1, m2, t |> -ms- d -ms> <| m1', m2', t' |> ->
  t' = zeroTime /\ t < d \/ t = t' +dt+ d. intros. inversion H. left.
  split. reflexivity. destruct d. destruct delay. apply cond_pos.
  right. assumption. left. split. reflexivity. assumption. Qed. 

Lemma delMStateTout : forall (m1 m2 : Mode) (a : ModeState) (d : Delay),
  <| m1, m2, zeroTime |> -ms- d -ms> a -> a = <| m1, m2, zeroTime |>.
  intros. inversion H. reflexivity. destruct (t' +dt+ d).
  unfold zeroTime in H5. destruct delay. inversion H5.
  clear H5. rewrite <- H7 in cond_pos. apply Rlt_irrefl in cond_pos.
  inversion cond_pos. reflexivity. Qed.

(** If an MState can timeout in d then it can timeout in d + d'.*)
Lemma delMStateToutLengthen : forall (m1 m2 : Mode) (t : Time) (d d' : Delay),
  <| m1, m2, t |>  -ms- d -ms> <| m1, m2, zeroTime |> ->
  <| m1, m2, t |>  -ms- d +d+ d' -ms> <| m1, m2, zeroTime |>. intros.
  inversion H. constructor. apply stepMsTimeout. rewrite H1.
  unfold zeroTime. destruct d, d'. unfold zeroNonneg.
  destruct delay, delay0. simpl. rewrite Rplus_comm.
  apply Rplus_le_lt_compat. apply Rle_refl. assumption.
  apply stepMsTimeout. eapply Rlt_trans. apply H1.
  replace (pos (delay d)) with (0 + d).
  destruct d, d'. destruct delay, delay0. simpl.
  rewrite Rplus_comm. apply Rplus_le_lt_compat.
  apply Rle_refl. assumption. ring. Qed.
  
(** If an Mstate is transitioning and it delays, then it is still transitioning.*)
Lemma delMStatePresTrans : forall (m1 m2 : Mode) (a : ModeState) (d : Delay) (t : Time),
  <| m1, m2, t|> -ms- d -ms> a -> exists t', a = <| m1, m2, t'|>.
  intros. inversion H. exists zeroTime. reflexivity.
  exists t'. reflexivity. exists zeroTime. reflexivity. Qed.

(** Two consecutive delays can be joined together into one delay, skipping the intermediate
state. The final delay is the sum of the two original delays.*)
Lemma delAddMState : forall (a a' a'' : ModeState) (d d' : Delay),
  a -ms- d -ms> a' -> a' -ms- d' -ms> a'' ->
  a -ms- d +d+ d' -ms> a''. intros. inversion H.
  rewrite <- H2 in H0. inversion H0. constructor.
  rewrite <- H2 in H0. apply delMStateTout in H0. rewrite H0.
  constructor. rewrite <- H4 in H0. addHyp H0.
  apply delMStatePresTrans in H0. invertClear H0. rename x into t''.
  rewrite H6. rewrite H6 in H5. clear H6.
  rewrite <- H2 in H. rewrite <- H4 in H.
  rewrite H3 in H. rewrite H3. apply delMStateTrans in H5.
  invertClear H5. invertClear H0. rewrite H5.
  apply stepMsTimeout. rewrite addDelayComm. destruct d, d', t'.
  destruct time, delay, delay0. simpl. apply Rplus_lt_le_compat.
  assumption. apply Rle_refl. rewrite H0.
  rewrite delTimeAddAssoc. constructor. rewrite addDelayComm.
  rewrite timeDelAddSwitch. reflexivity.
  rewrite <- H4 in H0. apply delMStateTout in H0. rewrite H0.
  rewrite <- H4 in H. rewrite H2. rewrite H4.
  rewrite <- H4. rewrite <- H2. apply delMStateToutLengthen.
  rewrite H2. assumption. Qed.

(** Every mode state can delay by any amount d.*)
Lemma delEnabledMState : forall (a : ModeState) (d : Delay),
  exists a', a -ms- d -ms> a'. intros.
  destruct a. exists m. constructor. addHyp (Rlt_le_dec t d).
  invertClear H. exists (<| m, m0, zeroTime |>).
  apply stepMsTimeout. assumption. apply delLeTimeSum in H0.
  invertClear H0. exists (<| m, m0, x |>). rewrite H.
  constructor. reflexivity. Qed.

(*The only way the current mode of a mode state can change is via an input on the
channel mCurr.*)
Lemma curr_switch_mState (k k' : ModeState) (a : ActModeState) :
  k -ms- a -ms> k' -> currModeMState k <> currModeMState k' ->
  a = chanMCurrWrite @?. intros H H0. invertClear H;
  try (false; apply H0; subst; reflexivity). reflexivity. Qed.

(** A mode output on mCurr is the current mode, and one on mNext is the next mode; neither
changes the mode state.*)
Lemma mState_curr_out k k' m : k -ms- chanMCurrRead .! m -ms> k' -> m = currModeMState k /\ k' = k.
Proof. intro S. inversion S; subst; split; reflexivity. Qed.

Lemma mState_next_out k k' m :
  k -ms- chanMNextRead .! m -ms> k' -> nextModeMState k = Some m /\ k' = k.
Proof. intro S. inversion S; subst; split; reflexivity. Qed.

Lemma timeSplit_mState (k k'' : ModeState) (d d' d'' : Delay) :
  k -ms- d'' -ms> k'' -> d'' = d +d+ d' ->
  exists k', k -ms- d -ms> k' /\ k' -ms- d' -ms> k''.
  (*Proof: This proof is fairly straightforward. We destruct k firstly*)
  destruct k.
  (*For the case where k is stable, the proof is trivial because the
  semantics allows k to delay to k by any amount, hence k' and k'' simply
  become k.*)
  introz U. exists m. inversion U. split; constructor.
  (*For the unstable case (i.e. a mode transition), well, each delay causes
  the guard to decrease and the resulting mode state is uniquely determined
  as the original with the value of the delay subtracted. Call the guard on
  the mode state in this case t. Then the assumed delay takes the guard from
  t to t - d'', whereas the intermediate state is a mode transition with
  guard t - d, which goest to t - d - d' = t - (d + d') = t - d''.*)
  introz U.
  (*Case analyse on d <= t or not.*)
  lets DT : Rle_or_lt d t. or_flat.
  (*In the ccase where d'' is less than t.*)
  rename OR into DT. remember (minusTime t d DT) as t'.
  exists (<| m, m0, t' |>). subst. split.
  constructor. apply timeEqR. simpl. ring.
  lets DMP : delMStatePresTrans U. ex_flat.
  subst. lets DMT : delMStateTrans U. or_flat. and_flat.
  subst. eapply stepMsTimeout. eapply Rplus_lt_reg_r.
  eapply Rle_lt_trans; [ | apply AND0]. apply Req_le.
  simpl. ring.
  subst. eapply stepMsDelGuard. apply timeEqR. simpl.
  ring.
  (*Otherwise t is less than d. In which case we can just use the
  timeout case.*)
  exists (<| m, m0, zeroTime |>). split. eapply stepMsTimeout.
  assumption. lets DMP : delMStatePresTrans U. ex_flat.
  subst. lets DMT : delMStateTrans U. or_flat. and_flat.
  subst. constructor. subst. false. eapply Rle_not_lt;
  [ | apply OR0]. simpl. rewrite Rplus_comm.
  rewrite Rplus_assoc. Rplus_le_tac. replace 0 with (0 + 0).
  apply Rplus_le_compat. apply Rlt_le. delPos. timeNonneg.
  ring. Qed.
  
(*LOCAL TIDY*)

(**A mode state is unstable if it is a transition from one mode to another.*)
Inductive unstable : ModeState -> Prop :=
  | unstbl m m' t : unstable (<| m , m' , t |>).

Lemma unstable_stable_in k : unstable k -> discActEnabledMState (chanMStableWrite *?) k.
  intros. inversion H. subst. repeat econstructor. Qed.

Lemma modeState_curr_enabled k :
  discActEnabledMState (chanMCurrRead ;! [baseMode (currModeMState k)]) k.
  destruct k; econstructor; constructor. Qed.

(** A mode state whose transition has timed out can take the switch on mCurr.*)
Lemma mst_tout_mCurr_in m1 m2 :
  discActEnabledMState (chanMCurrWrite *?) (<| m1, m2, zeroTime |>).
Proof. repeat econstructor. Qed.

Lemma mState_stable_next_enabled k m' : currModeMState k -mtr-> m' ->
  discActEnabledMState (chanMStableWrite*?) k \/
  discActEnabledMState (chanMNextWrite;? [baseMode m']) k.
  intros. destruct k. right. econstructor.
  lets SMI : stepMsInit H. apply SMI.
  left. econstructor. constructor. Qed.

Lemma next_modeState_stable_not k k' m' :
  nextModeMState k = Some m' -> k -ms- chanMStableRead @! -ms> k' -> False.
Proof.
  intros H Hs. destruct k; simpl in H; inversion Hs; subst; try discriminate.
Qed.

Lemma modeState_abort_in_not k k' :
  k -ms- chanAbort @? -ms> k' -> False.
Proof.
  intros H. inversion H. Qed.

Lemma unstable_stable_out_not k : unstable k ->
  ~ discActEnabledMState (chanMStableRead *!) k. unfold not. intros.
  inversion H. inversion H0. subst. inversion H3. Qed.

Lemma nextMode_unstable k m : nextModeMState k = Some m ->
  unstable k. intros. destruct k. inversion H.
  constructor. Qed.
 
(*-LOCAL TIDY*)
