
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
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.

Reserved Notation "e1 -EA- a ->> e2" (left associativity, at level 50).
Reserved Notation "e1 -ED- a ->> e2" (left associativity, at level 50).

Section EntityLanguage.
Context {PNames : ProcNames} {PDefs : ProcDefs} {PGuarded : GuardedDefs}.

(***************Messages*********************)


(** A message is a vector of values augmented with coverage and location information.*)
Record Message : Type :=
mkMsg
{
  msgPayload :> list BaseType;
  msgPos : Position;
  msgCoverage : Distance
}.
Notation "[- v , l , r -]" := (mkMsg v l r) (at level 40).

(** Extract the delivery radius from a broadcast.*)
Definition rangeMsg (m : Message) : Distance :=
   match m with [-v, l, r-] => r end.

(** Return the first mode that occurs in v, or None if there is no such mode.*)
Fixpoint firstMode (v : list BaseType) : option Mode :=
  match v with
  | [] => None
  | b :: vs => match b with
    | baseMode m => Some m
    | _ => firstMode vs
    end
  end.

(** modeBc b will return the first mode m, if it exists,
within the list of base values in b.*)
Definition modeBc (m : Message) : option Mode :=
  match m with [-v, l, r-] => firstMode v end.

(** Extract the position information from a broadcast. Note that this is the position
of the sending entity at the time of sending rather than delivery. The entity may have
moved between sending and delivery.*)
Definition posBc (m : Message) : Position :=
  match m with [-v, l, r-] => l end.



(*************** Syntax (and some other stuff) *********************)


(** And entity is a quadruple of components: An interface term, a software term,
an MState term and a location.*)
Record Entity : Type := mkEntity
{
  procEnt :> ProcTerm;
  posEnt :> Position;
  interEnt :> Interface;
  mstEnt : ModeState 
}.
Notation "[| p , l , i , k |]" := (mkEntity p l i k) (at level 30).

(** Equality on entities is decidable.*)
Lemma eqDecEnt : eqDec Entity. unfold eqDec.
  destruct x1, x2. addHyp (eqDecModeState mstEnt0 mstEnt1).
  addHyp (eqDecPosition posEnt0 posEnt1).
  addHyp (eqDecInterface interEnt0 interEnt1).
  addHyp (eqDecProcTerm procEnt0 procEnt1). invertClear H2.
  invertClear H. invertClear H0. invertClear H1. left.
  rewrite H2, H, H0, H3. reflexivity.
  right. unfold not. intro. apply H0. inversion H1. reflexivity.
  right. unfold not. intro. apply H. inversion H0. reflexivity.
  right. unfold not. intro. apply H2. inversion H. reflexivity.
  right. unfold not. intro. apply H3. inversion H2. reflexivity.
  Qed.

(** The current mode of an entity is the current mode of the mode state.*)
Coercion currModeEnt (e : Entity) : Mode :=
  match e with [|_, _, _, a|] => a end.

(** The next mode of an entity is the next mode of the mode state.*)
Definition nextModeEnt (e : Entity) : option Mode :=
  match e with [|_, _, _, a|] => nextModeMState a end.

(** incomingEnt v e means v is in the incoming list of the interface of e.*)
Inductive incomingEnt (v : list BaseType) : Entity -> Prop :=
  | incent P l h K : incomingInter v h -> incomingEnt v ([|P, l, h, K|]).

(** A predicate on processes, lifted to the entities whose software satisfies it.*)
Inductive liftProcEnt (X : ProcTerm -> Prop) : Entity -> Prop :=
  | lifpe (p : ProcTerm) (l : Position) (h : Interface) (k : ModeState) :
    X p -> liftProcEnt X ([|p, l, h, k|]).

(** An entity is initial for the seed process p0 when its software is p0 and its mode state
is a stable fail-safe mode: Definition 6.1 (p.133), with the protocol process as a
parameter.*)
Inductive initialEnt (p0 : ProcTerm) : Entity -> Prop :=
  | initEnt (l : Position) (h : Interface) (m : Mode) : failSafe m ->
    initialEnt p0 ([|p0, l, h, m|]).

Open Scope R_scope.

(** If the minimum distance of compatibiltiy of the respective modes
of the entities is less than or equal to the separation of the
entities in space, then they are compatible.*)
Definition compatible (e1 e2 : Entity) : Prop :=
  (minDistComp e1 e2) <= (dist2d e1 e2).
Notation "e1 ~~ e2" := (compatible e1 e2) (left associativity, at level 40).

(** Compatibility is a symmetric relation.*)
Lemma compatibleSymmetric : forall (e1 e2 : Entity), (e1 ~~ e2) <-> (e2 ~~ e1).
  unfold compatible. intros. split; intros; rewrite minDistCompSymmetric in H;
  rewrite distSymmetric in H; assumption. Qed.


(***************Semantics*********************)

(** A discrete action is either the input, output or ignorance of a message, or
it is the silent value tau.*)
Inductive ActDiscEnt : Type :=
  | aeTagOut : Message -> ActDiscEnt
  | aeTagIn : Message -> ActDiscEnt
  | aeTagIg : Message -> ActDiscEnt
  | aeTau : ActDiscEnt.
Notation "b #!" := (aeTagOut b) (at level 30).
Notation "b #?" := (aeTagIn b) (at level 30).
Notation "b #:" := (aeTagIg b) (at level 30).


(** The discrete action semantics for entities.*)
Inductive stepDiscEnt : Entity -> ActDiscEnt -> Entity -> Prop :=
  | stepDeProcTau : forall (p p' : ProcTerm) (l : Position) (i : Interface) (k : ModeState),
    p -PA- tauAct -PA> p' -> [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k |]
  | stepDeIOProcInter : forall (p p' : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list BaseType),
    p -PA- chanOutProc ;! v -PA> p' -> i -i- chanOutProc {? v -i> i' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i' , k |]
  | stepDeIOInterProc : forall (p p' : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list BaseType),
    p -PA- chanInProc ;? v -PA> p' -> i -i- chanInProc {! v -i> i' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i' , k |]
  | stepDeNotif : forall (p p' : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list BaseType),
    p -PA- chanAN ;? v -PA> p' -> i -i- chanAN {! v -i> i' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i' , k |]
  | stepDeRdStbl : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState),
    p -PA- chanMStableRead *? -PA> p' -> k -ms- chanMStableRead @! -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeWriteStbl : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState),
    p -PA- chanMStableWrite *! -PA> p' -> k -ms- chanMStableWrite @? -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeCurrWrite : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMCurrWrite *! -PA> p' -> k -ms- chanMCurrWrite @? -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeCurrRead : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMCurrRead ;? [baseMode m] -PA> p' -> k -ms- chanMCurrRead .! m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeNextWrite : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMNextWrite ;! [baseMode m] -PA> p' -> k -ms- chanMNextWrite .? m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeNextRead : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMNextRead ;? [baseMode m] -PA> p' -> k -ms- chanMNextRead .! m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDePosRead : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k : ModeState),
    p -PA- chanPos ;? [basePosition l] -PA> p' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k |]
  (** If the message sent was too far away, it gets ignored.*)
  | stepDeIgnore : forall (p : ProcTerm) (l l' : Position)
    (i : Interface) (k : ModeState) (v : list BaseType) (r : Distance),
     r < dist2d l l' -> 
    [| p , l , i , k |] -EA- [-v, l', r-]#: ->> [| p , l , i , k |]
  (** If the message sent was within range, then it gets input. This can be proven not
  to block by analysing the behaviour of interface components. Therefore, a message
  should always be accepted.*)
  | stepDeIn : forall (p : ProcTerm) (l l' : Position)
    (i i' : Interface) (k : ModeState) (v : list BaseType) (r : Distance),
    dist2d l l' <= r -> i -i- chanIOEnv {? v -i> i' ->
    [| p , l , i , k |] -EA- [-v, l', r-]#? ->> [| p , l , i' , k |]
  | stepDeOut : forall (p : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list BaseType) (r : Distance),
    i -i- chanIOEnv _! v !_ r -i> i' ->
    [| p , l , i , k |] -EA- [-v, l, r-]#! ->> [| p , l , i' , k |]
  | stepDeTest : forall (p : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    k -ms- chanMNextWrite .? m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p , l , i , k' |]
  where "e1 -EA- a ->> e2" := (stepDiscEnt e1 a e2).

(**An entity e is discrete action enabled for the discrete action a iff
there is some entity e' such that e transitions to e' via a.*)
Definition discActEnabledEnt (e : Entity) (a : ActDiscEnt) :=
  exists e', e -EA- a ->> e'.

(** This predicate says that it is impossible for p to synchronise with either i
or k via the discrete action a, and that a is not a read of the position: if p can do a,
then neither i nor k can do its complement, and a is not an input on chanPos. The last
clause is the thesis's (Definition 4.22, p.98). The position is always on offer to the
software, by the rule stepDePosRead, so a process that can read it must not let time
pass, just as one that can synchronise must not.*)
Definition noSyncNow (a : DiscAct) (p : ProcTerm)
  (i : Interface) (k : ModeState) : Prop :=
  discActEnabled p a ->
  (~discActEnabledInter (a^) i /\ ~discActEnabledMState (a^) k /\
  forall l : Position, a <> chanPos ;? [basePosition l]).

(** This predicate says that p i and k cannot synchronise now, nor can they
synchronise after each has respectively performed a delay of d' that is less
than d.*)
Definition noSync (p : ProcTerm) (i : Interface)
  (k : ModeState) (d : Delay) : Prop :=
  forall a : DiscAct, noSyncNow a p i k /\
  (forall (p' : ProcTerm) (i' : Interface) (k' : ModeState) (d' : Delay),
  d' < d -> p -PD- d' -PD> p' -> i -i- d' -i> i' -> k -ms- d' -ms> k' ->
  noSyncNow a p' i' k'). 

(** The timed action semantics for entities. There is only one delay law. The software,
mode state and interface components all must delay by the same amount d for the entire
entity to delay by this amount. After this, there are two interesting premises to the law.
The first deals with a displacement vector delta, saying that its absolute value must be
at most the delay multiplied by the maximum speed. In other words, movement is bounded.
The other premise that is of interest says that the components of the entity must not
be capable of synchronisation at any point during the delay.*)
Inductive stepTimedEnt : Entity -> Delay -> Entity -> Prop :=
  | stepTeDel : forall (d : Delay) (p p' : ProcTerm) (l delta : Position)
    (i i' : Interface) (k k' : ModeState),
    p -PD- d -PD> p' -> i -i- d -i> i' -> k -ms- d -ms> k' ->
    displacement delta <= speedMax * d -> noSync p i k d ->
    [| p , l , i , k |] -ED- d ->> [| p' , addPos l delta, i' , k' |]
  where "e1 -ED- d ->> e2" := (stepTimedEnt e1 d e2).


(*************** Results & Tactics *********************)


(**If the current mode has changed across a tau transition, then the software process
output on mCurr, and the mode state input on the same channel.*)
Theorem curr_switch_proc (p p' : ProcTerm) (l l' : Position) (h h' : Interface) (k k' : ModeState) :
  [|p, l, h, k|] -EA- aeTau ->> [|p', l', h', k'|] -> currModeMState k <> currModeMState k' ->
  p -PA- chanMCurrWrite *! -PA> p' /\ k -ms- chanMCurrWrite @? -ms> k'.
  intros H H0.
  (*By inversion on the discrete entity transition*)
  (*We first eliminate the cases where the mode state is the preserved.*)
  invertClear H; try (false; apply H0; assumption);
  (*We can then eliminate all cases where the the action is not tau,
  and simultaneously match our goal.*)  
  try (lets K : curr_switch_mState H10 H0; inversion K).
  (*Now we have this case which follows from assumptions.*)
  split;assumption.
  (*Finally we deal with a stray case that wasn't caught in our earlier elimination.*)
  lets K : curr_switch_mState H2 H0. inversion K. Qed.

(** The derivative of an ignore transition is the same as the source.*)
Theorem ignoreEqEnt : forall (e e' : Entity) (m : Message),
  e -EA- m#: ->> e' -> e = e'. intros. invertClear H. reflexivity. Qed.

(** An entity can always either input or ignore a message.*)
Theorem inOrIgEnt : forall (e : Entity) (m : Message),
  discActEnabledEnt e (m#?) \/ discActEnabledEnt e (m#:). intros.
  destruct m as [v l' r]. destruct e as [p l i k].
  addHyp (Rlt_or_le r (dist2d l l')). invertClear H. right.
  exists ([|p, l, i, k|]). apply stepDeIgnore. assumption. 
  left. addHyp (interfaceInEnabled i v). invertClear H.
  rename x into i'. exists ([|p, l, i', k|]).
  apply stepDeIn; assumption. Qed.

Lemma dec_compatible : forall (e1 e2 : Entity),
  e1 ~~ e2 \/ ~(e1 ~~e2).
Proof.
  intros. unfold compatible. destruct (Rle_dec (minDistComp e1 e2) (dist2d e1 e2));
  [left | right]; assumption. Qed.
(**Proof: Obvious*)

Lemma currMode_ent_mState : forall (p : ProcTerm) (l : Position) (h : Interface)
  (k : ModeState) (m : Mode), currModeEnt ([|p, l, h, k|]) = m -> currModeMState k = m.
Proof.
  intros. simpl in H. assumption. Qed.
(**Proof: Obvious from definitions*)

Lemma link_ent_inter_disc p p' l l' h h' k k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  h = h' \/ 
  (k = k' /\
  ((exists v, (h -i- chanOutProc {? v -i> h' /\ p -PA- chanOutProc;! v -PA> p')) \/
  (exists v, (h -i- chanInProc {! v -i> h' /\ p -PA- chanInProc;? v -PA> p')) \/
  (exists v, (h -i- chanAN {! v -i> h' /\ p -PA- chanAN;? v -PA> p')) \/
  (exists v, h -i- chanIOEnv {? v -i> h') \/
  (exists v r, h -i- chanIOEnv _! v !_ r -i> h'))).
  (*Inversion on entity transition and try LHS*)
  introz U. inversion U; subst; try (left; reflexivity); right;
  (split; [ reflexivity | ]).
  (*Now we do the other cases.*)
  left. exists v. split; assumption.
  right. left. exists v. split; assumption.
  right. right. left. exists v. split; assumption.
  do 3 right. left. exists v. assumption.
  do 4 right. exists v r. assumption. Qed.


Lemma link_ent_inter_del p p' l l' h h' k k' d :
  [|p, l, h, k|] -ED- d ->> [|p', l', h', k'|] ->
  h -i- d -i> h'. intros. inversion H. assumption. Qed.


Lemma link_ent_soft_del p p' l l' h h' k k' d :
  [|p, l, h, k|] -ED- d ->> [|p', l', h', k'|] ->
  p -PD- d -PD> p'. intros. inversion H. assumption. Qed.


Lemma link_ent_mState_del p p' l l' h h' k k' d :
  [|p, l, h, k|] -ED- d ->> [|p', l', h', k'|] ->
  k -ms- d -ms> k'. intros. inversion H. assumption. Qed.

(** If the software components of an entity transition are not equal, then
the transition is necessarily a tau action, and either the process performs a tau,
synchs with the interface, synchs with the mode state or reads the current position.*)
Lemma link_ent_proc_neq_disc p p' h h' l l' k k' a :
  p <> p' -> [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  a = aeTau /\ ( 
  p -PA- tauAct -PA> p' \/
  (exists h' c v, p -PA- c ;! v -PA> p' /\ h -i- c {? v -i> h') \/
  (exists h' c v, p -PA- c ;? v -PA> p' /\ h -i- c {! v -i> h') \/
  (exists k' c m, p -PA- c ;! [baseMode m] -PA> p' /\ k -ms- c .? m -ms> k') \/
  (exists k' c m, p -PA- c ;? [baseMode m] -PA> p' /\ k -ms- c .! m -ms> k') \/
  (exists k' c, p -PA- c *! -PA> p' /\ k -ms- c @? -ms> k') \/
  (exists k' c, p -PA- c *? -PA> p' /\ k -ms- c @! -ms> k') \/
  p -PA- chanPos ;? [basePosition l] -PA> p').
  intros. inversion H0; (split;[ try reflexivity | ]);
  try (subst; contradict H; reflexivity).
  left; repeat eexists; eassumption.
  right; left; repeat eexists; eassumption.
  right. right. left. repeat eexists; eassumption.
  right. right. left. repeat eexists; eassumption.
  do 6 right. left. repeat eexists; eassumption.
  do 5 right. left. repeat eexists; eassumption.
  do 5 right. left. repeat eexists; eassumption.
  do 4 right. left. repeat eexists; eassumption.
  do 3 right. left. repeat eexists; eassumption.
  do 4 right. left. repeat eexists; eassumption.
  repeat right. repeat eexists; eassumption.
  Qed.

(** A discrete entity transition either leaves the software unchanged or the software takes a step.*)
Lemma link_ent_soft_disc p p' l l' h h' k k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p = p' \/ exists b, p -PA- b -PA> p'.
Proof.
  intro H. inversion H; subst;
  first [left; reflexivity | right; eexists; eassumption].
Qed.

(***************Components of the software*********************)
(** When an entity's software is a parallel composition, a step of the entity is taken down
to the components, for any number of them: forward, from the components before the step,
and between the components before and after it when both are known as compositions of as
many components. The number matters, since the same term is also a composition of fewer
components.*)

(** A discrete step leads to a composition of as many components, each unchanged or
stepped once.*)
Lemma ent_disc_comps_fwd q qs l h k e' a :
  [|parAll q qs, l, h, k|] -EA- a ->> e' ->
  exists q' qs' l' h' k', e' = [|parAll q' qs', l', h', k'|] /\
  Forall2 (fun x x' => x = x' \/ exists b, x -PA- b -PA> x') (q :: qs) (q' :: qs').
Proof.
  intro S. destruct e' as [p' l' h' k'].
  destruct (link_ent_soft_disc _ _ _ _ _ _ _ _ _ S) as [E | [b B]].
  - subst p'. exists q qs l' h' k'. split; [reflexivity | ].
    apply Forall2_diag. intros x _. left. reflexivity.
  - destruct (parAll_disc_weak _ _ _ _ B) as [q' [qs' [E F]]]. subst p'.
    exists q' qs' l' h' k'. split; [reflexivity | exact F].
Qed.

(** Across a discrete step between compositions of as many components, each component is
unchanged or stepped once.*)
Lemma ent_disc_comps q qs q' qs' l l' h h' k k' a :
  [|parAll q qs, l, h, k|] -EA- a ->> [|parAll q' qs', l', h', k'|] ->
  length qs = length qs' ->
  Forall2 (fun x x' => x = x' \/ exists b, x -PA- b -PA> x') (q :: qs) (q' :: qs').
Proof.
  intros S L. destruct (ent_disc_comps_fwd _ _ _ _ _ _ _ S) as [r [rs [l2 [h2 [k2 [E F]]]]]].
  injection E as E _ _ _.
  assert (LR : length qs = length rs)
    by (apply Forall2_length in F; simpl in F; injection F; trivial).
  destruct (parAll_inj _ _ _ _ E) as [E1 E2]; [congruence | ]. subst r rs. exact F.
Qed.

(** A delay leads to a composition of as many components, each delayed by it.*)
Lemma ent_del_comps_fwd q qs l h k e' d :
  [|parAll q qs, l, h, k|] -ED- d ->> e' ->
  exists q' qs' l' h' k', e' = [|parAll q' qs', l', h', k'|] /\
  Forall2 (fun x x' => x -PD- d -PD> x') (q :: qs) (q' :: qs').
Proof.
  intro S. destruct e' as [p' l' h' k']. lets D : link_ent_soft_del S.
  destruct (parAll_del_inv _ _ _ _ D) as [q' [qs' [E F]]]. subst p'.
  exists q' qs' l' h' k'. split; [reflexivity | exact F].
Qed.

(** Across a delay between compositions of as many components, each component delays by
it.*)
Lemma ent_del_comps q qs q' qs' l l' h h' k k' d :
  [|parAll q qs, l, h, k|] -ED- d ->> [|parAll q' qs', l', h', k'|] ->
  length qs = length qs' ->
  Forall2 (fun x x' => x -PD- d -PD> x') (q :: qs) (q' :: qs').
Proof.
  intros S L. destruct (ent_del_comps_fwd _ _ _ _ _ _ _ S) as [r [rs [l2 [h2 [k2 [E F]]]]]].
  injection E as E _ _ _.
  assert (LR : length qs = length rs)
    by (apply Forall2_length in F; simpl in F; injection F; trivial).
  destruct (parAll_inj _ _ _ _ E) as [E1 E2]; [congruence | ]. subst r rs. exact F.
Qed.

(** Take software that uses the channels in ics only for input and those in ocs only for output,
and a component of it that can only have changed by acting on one of these channels. Either the
component stayed as it was, or the entity's step was the component meeting the rest of the
entity. That is, put alone in the entity, the component makes the same step, to the same
position, interface and mode state, and every other component stayed as it was. That step is
not silent, since the component acts on a channel, so it meets the mode state or the interface,
or reads the position.*)
Lemma ent_disc_comp_chan ics ocs q qs q' qs' l l' h h' k k' a i x x' :
  oneWayUsage ics ocs (parAll q qs) ->
  [|parAll q qs, l, h, k|] -EA- a ->> [|parAll q' qs', l', h', k'|] -> length qs = length qs' ->
  nth_error (q :: qs) i = Some x -> nth_error (q' :: qs') i = Some x' ->
  (forall b, x -PA- b -PA> x' -> oneWayAct ics ocs b) ->
  x = x' \/
  stepAt (fun y y' => [|y, l, h, k|] -EA- a ->> [|y', l', h', k'|]) i (q :: qs) (q' :: qs').
Proof.
  intros U S L Nx Nx' ACT. inversion S; subst;
    first
    [ (* the software stays *)
      match goal with [E : parAll _ _ = parAll _ _ |- _] =>
        destruct (parAll_inj _ _ _ _ E ltac:(congruence)) as [E1 E2]; subst; left; congruence end
    | (* the software steps, and the component takes the step with the rest of the entity *)
      match goal with [T : parAll q qs -PA- _ -PA> parAll q' qs' |- _] =>
        destruct (parAll_disc_chan _ _ _ _ _ _ _ _ _ _ U T L Nx Nx' ACT) as [E | St];
        [left; exact E | right; eapply stepAt_impl; [ | exact St];
          intros y y' Y; cbv beta in Y; solve [econstructor; eassumption]] end ].
Qed.

(***************Modes of an entity, and reachable entities*********************)

(** A delay changes neither the current mode nor the next mode of an entity: the mode state
only counts its transition timer down.*)
Lemma stepTimedEnt_currMode e e' d : e -ED- d ->> e' -> currModeEnt e = currModeEnt e'.
Proof.
  intro S. inversion S; subst. simpl.
  match goal with [K : _ -ms- _ -ms> _ |- _] => inversion K; subst; reflexivity end.
Qed.

Lemma stepTimedEnt_nextMode e e' d : e -ED- d ->> e' -> nextModeEnt e = nextModeEnt e'.
Proof.
  intro S. inversion S; subst. simpl.
  match goal with [K : _ -ms- _ -ms> _ |- _] => inversion K; subst; reflexivity end.
Qed.

(** The entities reachable from an initial entity for p0 by any number of discrete steps and
delays: reachability as Definition 6.2 (p.133) has it, for one entity.*)
Inductive reachableEnt (p0 : ProcTerm) : Entity -> Prop :=
  | reachEntInit (e : Entity) : initialEnt p0 e -> reachableEnt p0 e
  | reachEntDisc (e e' : Entity) (a : ActDiscEnt) : reachableEnt p0 e ->
    e -EA- a ->> e' -> reachableEnt p0 e'
  | reachEntDel (e e' : Entity) (d : Delay) : reachableEnt p0 e ->
    e -ED- d ->> e' -> reachableEnt p0 e'.

(** The software of a reachable entity is reachable from p0.*)
Lemma reachableEnt_proc p0 e : reachableEnt p0 e -> reachableFrom p0 (procEnt e).
Proof.
  intro R. induction R as [e I | e e' a R IH S | e e' d R IH S].
  - inversion I; subst. apply reachableFromBase.
  - destruct e as [p l h k]. destruct e' as [p' l' h' k']. simpl in *.
    destruct (link_ent_soft_disc _ _ _ _ _ _ _ _ _ S) as [EQ | [b B]].
    + subst. exact IH.
    + eapply reachableFromDisc; eassumption.
  - destruct e as [p l h k]. destruct e' as [p' l' h' k']. simpl in *.
    eapply reachableFromDel; [exact IH | ]. eapply link_ent_soft_del. exact S.
Qed.

(** A delaying entity has no synchronisation on offer between its components.*)
Lemma ent_del_noSyncNow p l h k d e' :
  [|p, l, h, k|] -ED- d ->> e' -> forall a, noSyncNow a p h k.
Proof.
  intros DEL a. inversion DEL; subst.
  match goal with [B : noSync _ _ _ _ |- _] => apply B end.
Qed.

(** No delay while the software can synchronise with the mode state.*)
Lemma ent_del_sync_mState_not p l h k d e' a : discActEnabled p a ->
  discActEnabledMState (a^) k -> [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros DA DM DEL. destruct (ent_del_noSyncNow _ _ _ _ _ _ DEL a DA) as [_ [NM _]].
  apply NM. assumption.
Qed.

(** No delay while the software can synchronise with the interface.*)
Lemma ent_del_sync_inter_not p l h k d e' a : discActEnabled p a ->
  discActEnabledInter (a^) h -> [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros DA DI DEL. destruct (ent_del_noSyncNow _ _ _ _ _ _ DEL a DA) as [NI _].
  apply NI. assumption.
Qed.

(** No delay while the software can read a position: the entity's own is always on offer.*)
Lemma ent_del_pos_in_not p l h k d e' l0 :
  discActEnabled p (chanPos ;? [basePosition l0]) -> [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros DA DEL. destruct (ent_del_noSyncNow _ _ _ _ _ _ DEL _ DA) as [_ [_ NP]].
  apply (NP l0). reflexivity.
Qed.

(** Software that reads any current mode cannot let time pass: the mode state always
offers its current mode.*)
Lemma ent_del_mCurr_in_not p l h k d e' :
  (forall m, discActEnabled p (chanMCurrRead ;? [baseMode m])) ->
  [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros DA DEL. eapply ent_del_sync_mState_not;
  [apply (DA (currModeMState k)) | | exact DEL].
  simpl. apply modeState_curr_enabled.
Qed.

(** Software that reads stability and any next mode cannot let time pass: a stable mode
state offers mStable and an unstable one offers its next mode on mNext.*)
Lemma ent_del_mStable_mNext_in_not p l h k d e' :
  discActEnabled p (chanMStableRead *?) ->
  (forall m, discActEnabled p (chanMNextRead ;? [baseMode m])) ->
  [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros DS DN DEL. destruct k as [m1 | m1 m2 t].
  - eapply ent_del_sync_mState_not; [exact DS | | exact DEL].
    simpl. econstructor. apply stepMsOutStable.
  - eapply ent_del_sync_mState_not; [apply (DN m2) | | exact DEL].
    simpl. econstructor. apply stepMsOutNext.
Qed.

(** A discrete entity step keeps every notification with a positive timestamp.*)
Lemma stepEnt_disc_pres_notif_pos p p' l l' k k' li li' lo lo' ln ln' b v t :
  [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
  [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
  <( v, t )> _: notifList ln -> 0 < t -> <( v, t )> _: notifList ln'.
Proof.
  intros H Hin Ht. inversion H; subst; try assumption;
  match goal with [Hi : _ -i- _ -i> _ |- _] => inversion Hi; subst; try assumption end.
  - eapply notifList_out_pres_pos; eassumption.
  - eapply notifList_in_pres; eassumption.
Qed.

(** A discrete entity step keeps every outgoing message, unless it is the entity broadcasting
that message from its position, which needs the message's timestamp to have run out.*)
Lemma stepEnt_disc_out p p' l l' k k' li li' lo lo' ln ln' b v t :
  [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
  [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
  <( v, t )> _: outList lo ->
  <( v, t )> _: outList lo' \/ (t = zeroTime /\ exists r, b = [-v, l, r-] #!).
Proof.
  intros H Hin. inversion H; subst; try (left; assumption);
  match goal with [Hi : _ -i- _ -i> _ |- _] => inversion Hi; subst; try (left; assumption) end.
  - left. eapply outList_buff_pres; eassumption.
  - match goal with [Ho : _ -ol- _ !! -ol> _ |- _] => inversion Ho; subst end.
    match goal with [Ht : _ -tl- _ !! -tl> _ |- _] =>
      destruct (timedList_out _ _ _ _ Ht Hin) as [IN' | EQ] end.
    + left. exact IN'.
    + injection EQ as EQv EQt. subst. right. split; [reflexivity | ]. eexists. reflexivity.
Qed.


(** Scaling a vector by a non-negative factor scales its displacement by the same factor.*)
Local Lemma displacement_scale (s x y : R) : 0 <= s ->
  nonneg (displacement (mkPosition (s * x) (s * y))) =
  s * nonneg (displacement (mkPosition x y)).
Proof.
  intros. unfold displacement, dist2d, origin, dist_euc. simpl.
  replace (Rsqr (s * x - 0) + Rsqr (s * y - 0)) with
    (Rsqr s * (Rsqr (x - 0) + Rsqr (y - 0))) by (unfold Rsqr; ring).
  rewrite sqrt_mult_alt by apply Rle_0_sqr. rewrite sqrt_Rsqr by assumption.
  reflexivity.
Qed.

Lemma timeSplit_ent e e'' d d' d'' :
  e -ED- d'' ->> e'' -> d'' = d +d+ d' ->
  exists e', e -ED- d ->> e' /\ e' -ED- d' ->> e''.
Proof using PNames PDefs.
  intros ED EQ. inversion ED as [d0 p p'' l delta i i'' k k'' PD ID KD DISP NS]; subst.
  lets TSP : timeSplit PD (eq_refl (d +d+ d')). destruct TSP as [p' [PD1 PD2]].
  lets TSI : timeSplit_inter ID (eq_refl (d +d+ d')). destruct TSI as [i' [ID1 ID2]].
  lets TSK : timeSplit_mState KD (eq_refl (d +d+ d')). destruct TSK as [k' [KD1 KD2]].
  assert (DP : 0 < pos (delay d)) by (destruct d as [[r rp]]; simpl; assumption).
  assert (DP' : 0 < pos (delay d')) by (destruct d' as [[r rp]]; simpl; assumption).
  set (r := pos (delay d)) in *. set (r' := pos (delay d')) in *.
  assert (SUM : pos (delay (d +d+ d')) = r + r') by reflexivity.
  set (s1 := r / (r + r')). set (s2 := r' / (r + r')).
  assert (S1 : 0 <= s1) by (unfold s1; apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  assert (S2 : 0 <= s2) by (unfold s2; apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  destruct delta as [x y].
  exists ([|p', addPos l (mkPosition (s1 * x) (s1 * y)), i', k'|]).
  rewrite SUM in DISP.
  set (D := nonneg (displacement (mkPosition x y))) in *.
  split.
  (*First step*)
  constructor; try assumption.
  rewrite displacement_scale by assumption. fold D.
  apply Rle_trans with (s1 * (speedMax * (r + r'))).
  apply Rmult_le_compat_l; assumption.
  right. unfold s1. change (pos (delay d)) with r. field. lra.
  intro a. destruct (NS a) as [NS1 NS2]. split. assumption.
  intros p2 i2 k2 d2 LT P2 I2 K2. apply (NS2 p2 i2 k2 d2); try assumption.
  rewrite SUM. unfold r, r' in *. lra.
  (*Second step*)
  replace (addPos l (mkPosition x y)) with
    (addPos (addPos l (mkPosition (s1 * x) (s1 * y))) (mkPosition (s2 * x) (s2 * y))).
  constructor; try assumption.
  rewrite displacement_scale by assumption. fold D.
  apply Rle_trans with (s2 * (speedMax * (r + r'))).
  apply Rmult_le_compat_l; assumption.
  right. unfold s2. change (pos (delay d')) with r'. field. lra.
  intro a. destruct (NS a) as [NS1 NS2]. split.
  apply (NS2 p' i' k' d); try assumption. rewrite SUM. unfold r, r' in *. lra.
  intros p2 i2 k2 d2 LT PD3 ID3 KD3. apply (NS2 p2 i2 k2 (d +d+ d2)).
  rewrite SUM. simpl. unfold r, r' in *. lra.
  eapply delAddSoft; eassumption.
  eapply delAddInter; eassumption.
  eapply delAddMState; eassumption.
  assert (E : s1 + s2 = 1) by (unfold s1, s2; field; lra).
  unfold addPos. simpl. f_equal.
  transitivity (xCoord l + (s1 + s2) * x). ring. rewrite E. ring.
  transitivity (yCoord l + (s1 + s2) * y). ring. rewrite E. ring.
Qed.
(**Proof: This should follow from time split properties of the underlying components. Also, it would have to be shown that the noSynch predicate would still hold for the intermediate entity component e', with the time parameter changed.*)


(*LOCAL TIDY*)










(*-LOCAL TIDY*)

(** A discrete action doesn't move an entity.*)
Lemma stepEnt_disc_pres_pos (e e' : Entity) a :
  e -EA- a ->> e' -> posEnt e = posEnt e'. intros.
  destruct e, e'. inversion H; reflexivity. Qed.

(** The software step inside a discrete entity step, when there is one: if it is an input on
chanPos, the value read is the entity's position, since only the position read rule
matches such an input. Likewise a mode read on mCurr or mNext is the mode state's current
or next mode, and leaves the mode state as it was.*)
Lemma ent_disc_proc_act p l h k p' l' h' k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p = p' \/ exists c, p -PA- c -PA> p' /\
    (forall v, c = chanPos ;? [basePosition v] -> v = l) /\
    (forall m, c = chanMCurrRead ;? [baseMode m] -> m = currModeMState k /\ k' = k) /\
    (forall m, c = chanMNextRead ;? [baseMode m] -> nextModeMState k = Some m /\ k' = k).
Proof.
  intro S. inversion S; subst; try (left; reflexivity); right;
    match goal with [T : _ -PA- ?c -PA> _ |- _] => exists c; split; [exact T | ] end;
    (split; [ | split]); intros vv E; try congruence.
  - injection E as E; subst. apply mState_curr_out. assumption.
  - injection E as E; subst. apply mState_next_out. assumption.
Qed.

(** Likewise a write on mCurr, mNext or mStable is taken by the mode state.*)
Lemma ent_disc_proc_write p l h k p' l' h' k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p = p' \/ exists c, p -PA- c -PA> p' /\
    (c = chanMCurrWrite *! -> k -ms- chanMCurrWrite @? -ms> k') /\
    (c = chanMStableWrite *! -> k -ms- chanMStableWrite @? -ms> k') /\
    (forall m, c = chanMNextWrite ;! [baseMode m] -> k -ms- chanMNextWrite .? m -ms> k').
Proof.
  intro S. inversion S; subst; try (left; reflexivity); right;
    match goal with [T : _ -PA- ?c -PA> _ |- _] => exists c; split; [exact T | ] end;
    (split; [ | split]); intros; congruence.
Qed.

End EntityLanguage.

(** A section's notations and tactics end with it. So that later files can use them, the
notations are declared again here, and the tactics are declared here.*)
Notation "[- v , l , r -]" := (mkMsg v l r) (at level 40).
Notation "[| p , l , i , k |]" := (mkEntity p l i k) (at level 30).
Notation "e1 ~~ e2" := (compatible e1 e2) (left associativity, at level 40).
Notation "b #!" := (aeTagOut b) (at level 30).
Notation "b #?" := (aeTagIn b) (at level 30).
Notation "b #:" := (aeTagIg b) (at level 30).
Notation "e1 -EA- a ->> e2" := (stepDiscEnt e1 a e2).
Notation "e1 -ED- d ->> e2" := (stepTimedEnt e1 d e2).

(*Destruct an entity and then its interface component*)
Ltac destr_ent_inter e p l k li lo ln := let h := fresh in destruct e as [p l h k];
  destruct h as [li lo ln].

(*Adds the result stepDisc_ent_inter to the hypotheses and splits it up and tidies it.*)
Ltac link_entinterdisc_tac v r U := 
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -EA- ?a ->> [|?p', ?l', ?h', ?k'|] |- _] =>
    let H1 := fresh in lets H1 : link_ent_inter_disc H;
    let U1 := fresh U in let H0 := fresh in 
    (*Break off first disjunct as U1, leave H0 as chunk*)
    elim_intro H1 U1 H0;[ | 
    let H7 := fresh in let H8 := fresh in
    (*Break conjunction H0 into H7 and H8*)
    decompAnd2 H0 H7 H8; let V := fresh v in
    (*Break H8 up into 5 disjuncts*)
    elimOr5 H8 U;
    [(let H2 := fresh in destruct U1 as [V H2]; 
    andflat U).. | let H2 := fresh in destruct U1 as [V H2]; rename H2 into U1 | 
    let R := fresh r in let H3 := fresh in
    decompEx2 U1 V R H3;rename H3 into U1 ]
    ]
  end.

Ltac link_entinterdel_tac U :=
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -ED- ?d ->> [|?p', ?l', ?h', ?k'|] |- _] =>
  let U1 := fresh U in lets U1 : link_ent_inter_del H
  end.

Ltac link_entsoftdel_tac U :=
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -ED- ?d ->> [|?p', ?l', ?h', ?k'|] |- _] =>
  let U1 := fresh U in lets U1 : link_ent_soft_del H
  end.

Ltac link_entmstatedel_tac U :=
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -ED- ?d ->> [|?p', ?l', ?h', ?k'|] |- _] =>
  let U1 := fresh U in lets U1 : link_ent_mState_del H
  end.

(** Destructs the next entity it encounters naming its sub-components as fresh instances
of p, l, h, k.*)
Ltac destrEnt p l h k :=
  match goal with
  [ e : Entity |- _ ] =>
  let vp := fresh p in let vl := fresh l in
  let vh := fresh h in let vk := fresh k in
  destruct e as [vp vl vh vk]
  end.

(** Repeatedly destructs all entities according to the names given.*)
Ltac destrEnts p l h k := repeat destrEnt p l h k.

(**Destructs any entities it finds. May have also be searched for as destr_ents.*)
Ltac destrEnts_norm := let p := fresh "p" in let l := fresh "l" in
  let h := fresh "h" in let k := fresh "k" in destrEnts p l h k.

(** From a delay on an entity creates the hypothesis NS (a parameter) that no synchronisation
is possible between any of the components of the entity.*)
Ltac del_noSync_tac NS :=
  match goal with [a : DiscAct, U : [|?p0, _, ?h0, ?k0|] -ED- ?d ->> _ |- _] =>
  assert (noSync p0 h0 k0 d) as NS; [inversion U; assumption | ]
  end.

(** From a hypothesis X of noSynch between various components, creates a weakened version of X
saying that noSyncNow is possible between those components and calls it NS.*)
Ltac noSync_noSyncNow_tac NS := 
  match goal with
  [ a : DiscAct, X : noSync ?p0 ?h0 ?k0 _ |- _] =>
  assert (noSyncNow a p0 h0 k0) as NS; [unfold noSync in X; apply X
  | ] end.

(** From an entity delay creates the hypothesis NS saying that noSyncNow is possible between
the components of the entity, via the first action a matched in the hypotheses.*)
Ltac del_noSyncNow_tac NS :=
  let X := fresh in del_noSync_tac X; noSync_noSyncNow_tac NS;
  clear X.

(**Takes a delay hypothesis and inverts to give that noSyncNow holds for
the components of the entity in question.*)
Ltac noSyncNow_tac := match goal with
  [A : [|?p, _, ?h, ?k|] -ED- ?d ->> _ |- _] =>
  let NS := fresh "NS" in
  assert (forall a, noSyncNow a p h k) as NS;
  [inversion A; match goal with [B : noSync p h k d |- _] =>
  apply B end| ] end.

(*Inverts an entity delay to a process delay*)
Ltac invertDel_ent_proc := match goal with
  [U1 : [|?p0, _, _, _|] -ED- ?d ->> [|?p, _, _, _|] |- _ ]
  => assert (p0 -PD- d -PD> p) as PD; [inversion U1; assumption | ] end.
