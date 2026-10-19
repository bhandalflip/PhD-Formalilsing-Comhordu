(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** The software component of the language is here defined. The language is generic in its
process names and their definitions: a protocol supplies them as instances of the classes
ProcNames and ProcDefs below. Some results also need the definitions to be guarded, which a
protocol shows with an instance of GuardedDefs. For the Comhordú protocol, see Protocol.v and
ProtocolBridge.v.*)

Require ComhCoq.lib.Extras.LibTactics.
Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Lists.ListSet.
From Stdlib Require Import Lia.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.

(******************Syntax*******************)

(**Names for defining parametrised processes. A protocol supplies them, and equality on
them must be decidable.*)
Class ProcNames := {
  Name : Type;
  eqDecName : eqDec Name }.

Section Syntax.
Context {PNames : ProcNames}.

(**The set of process terms, which may have free variables in them.*)
Inductive ProcTerm : Type :=
  | nilProc : ProcTerm
  | outPrefix : Channel -> list Exp -> ProcTerm -> ProcTerm
  | inPrefix : Channel -> list Var -> ProcTerm -> ProcTerm
  | ifThen : BoolExp -> ProcTerm -> ProcTerm
  | sum : ProcTerm -> ProcTerm -> ProcTerm
  | parComp : ProcTerm -> ProcTerm -> ProcTerm
  | app : Name -> list Exp -> ProcTerm
  | del : Exp -> ProcTerm -> ProcTerm.

(** Equality is decidable on ProcTerms.*)
Lemma eqDecProcTerm : eqDec ProcTerm. unfold eqDec.
  induction x1; induction x2; try solve [right; unfold not; intros; inversion H];
  try solve [left; reflexivity]; try solve [addHyp (IHx1 x2);
  invertClear H; [left; subst; reflexivity | right;
  unfold not; intros ; apply H0; inversion H ; reflexivity]].
  addHyp (eqDecChannel c c0);
  addHyp (IHx1 x2); addHyp (list_eq_dec eqDecExp l l0);
  invertClear H; [invertClear H0;[invertClear H1; [left; subst; reflexivity|
  right; unfold not; intros; apply H0; invertClear H1; reflexivity] |
  right; unfold not; intros; apply H; invertClear H0; reflexivity] |
  right; unfold not; intros; apply H2; invertClear H; reflexivity].
  addHyp (eqDecChannel c c0); addHyp (IHx1 x2).
  addHyp (list_eq_dec eqDecVar l l0);
  invertClear H; [invertClear H0;[invertClear H1; [left; subst; reflexivity|
  right; unfold not; intros; apply H0; invertClear H1; reflexivity] |
  right; unfold not; intros; apply H; invertClear H0; reflexivity] |
  right; unfold not; intros; apply H2; invertClear H; reflexivity].
  addHyp (eqDecBoolExp b b0). invertClear H.
  addHyp (IHx1 x2); invertClear H; [left; subst; reflexivity | right;
  unfold not; intros ; apply H1; inversion H ; reflexivity].
  right. unfold not; intros. apply H0. inversion H. reflexivity.
  addHyp (IHx1_1 x2_1). invertClear H. addHyp (IHx1_2 x2_2).
  invertClear H. left. subst. reflexivity. right.
  unfold not. intros. apply H1. inversion H. reflexivity.
  right. unfold not. intros. apply H0. inversion H. reflexivity.
  addHyp (IHx1_1 x2_1). invertClear H. addHyp (IHx1_2 x2_2).
  invertClear H. left. subst. reflexivity. right.
  unfold not. intros. apply H1. inversion H. reflexivity.
  right. unfold not. intros. apply H0. inversion H. reflexivity.
  addHyp (eqDecName n n0). invertClear H.
  addHyp (list_eq_dec eqDecExp l l0). invertClear H. left. subst.
  reflexivity. right. unfold not. intros. apply H1. inversion H.
  reflexivity. right. unfold not. intros. apply H0. inversion H.
  reflexivity. addHyp (IHx1 x2). invertClear H.
  addHyp (eqDecExp e e0). invertClear H. left. subst. reflexivity.
  right. unfold not. intros. apply H1. inversion H.
  reflexivity. right. unfold not. intros. apply H0. inversion H.
  reflexivity. Qed.









(** The parallel composition of one or more processes, nested to the right as the notation
$||$ parses, so that parAll p1 [p2, p3] is p1 $||$ p2 $||$ p3. A result about any number
of components is stated once, about it.*)
Fixpoint parAll (p : ProcTerm) (ps : list ProcTerm) : ProcTerm :=
  match ps with
  | [] => p
  | q :: qs => parComp p (parAll q qs)
  end.

End Syntax.

(** Process language syntactic sugar.*)
Notation "c $< l >$ ? P" := (inPrefix c l P) (at level 41, right associativity).
Notation "c $< l >$ ! P" := (outPrefix c l P) (at level 41, right associativity).
Notation "c ? P" := (inPrefix c [] P) (at level 41, right associativity).
Notation "c ! P" := (outPrefix c [] P) (at level 41, right associativity).
Notation "B $> P" := (ifThen B P) (at level 41, right associativity).
Notation "P $+$ Q" := (sum P Q) (at level 50).
Notation "P $||$ Q" := (parComp P Q) (at level 45, right associativity).
Notation "h $( l )$" := (app h l) (at level 41, right associativity).
Notation " $< E >$ P " := (del E P) (at level 41, right associativity).

(**Redefining pair notation as it was overwritten by interval notation for real numbers.*)
Notation "( a , b )" := (pair a b).

(**The definition relation. It maps every name to a list of variables and a process
term. The meaning of def n = (xs, p) is that n applied to xs is defined to be p.
A protocol supplies it.*)
Class ProcDefs {PNames : ProcNames} := {
  def : Name -> (list Var * ProcTerm) }.

Section Semantics.
Context {PNames : ProcNames} {PDefs : ProcDefs}.

(*******************Discrete Semantics*******************)

(**Susbstitution of expressions for variables in a term. Essentially maps
the substitution across the term, calling on expression substitution in the
meantime.*)
Fixpoint subProcTerm (s : Subst) (t : ProcTerm) : ProcTerm :=
  match t with
  | nilProc => nilProc
  | outPrefix c l t' => outPrefix c (listSub s l) (subProcTerm s t')
  (*Reset the terms in the list l because they are bound.*)
  | inPrefix c l t' => inPrefix c l (subProcTerm (resetSub s l) t')
  | ifThen b t' => ifThen (subBoolExp s b) (subProcTerm s t')
  | sum t1 t2 => sum (subProcTerm s t1) (subProcTerm s t2)
  | parComp t1 t2 => parComp (subProcTerm s t1) (subProcTerm s t2)
  | app n l => app n (listSub s l)
  | del e t' => del (subExp s e) (subProcTerm s t')
  end.

(**An action is either discrete or timed.*)
Inductive Act :=
  | actDisc :> DiscAct -> Act
  | actTime :> Delay -> Act.

(** The duration of an action. A discrete action has duration 0,
while a delay has a duration equal to the amount of the delay.*)
Definition durationSoft (a : Act) : Time :=
  match a with
  | actDisc _ => zeroTime
  | actTime d => d
  end. 

(**The discrete action semantics over process terms. The triple p d q is a member
of this relation iff the process p can perform the discrete action d and evolve
to the process q.*)
Inductive stepDiscProc : ProcTerm -> DiscAct -> ProcTerm -> Prop :=
  | stepDpOut : forall (c : Channel) (l1 : list Exp) (l2 : list BaseType) (p : ProcTerm),
    evalExpLists l1 l2 -> stepDiscProc (outPrefix c l1 p) (outAct c l2) p
  (** If the base values l1 are typed for the variables l2, one value of each variable's
    type, then they can be input across the channel in question, and the resulting term is
    the guarded term with all occurrences of variables in the list l2 replaced by their
    base value counterparts in l1. The thesis defines the semantics only over well-typed
    processes (Remark 4.1, p.65); the typing premise is what makes that so here.*)
  | stepDpIn : forall (c : Channel) (l1 : list BaseType) (l2 : list Var) (p : ProcTerm),
    typedVals l2 l1 -> stepDiscProc (inPrefix c l2 p) (inAct c l1)
    (subProcTerm (listsToSub l2 (listBaselistExp l1)) p)
  | stepDpThen : forall (b : BoolExp) (p p' : ProcTerm) (d : DiscAct),
    stepDiscProc p d p' -> evalBoolExpFunTot b = true ->
    stepDiscProc (ifThen b p) d p'
  | stepDpChoiceL : forall (p1 p2 p' : ProcTerm) (d : DiscAct),
    stepDiscProc p1 d p' -> stepDiscProc (sum p1 p2) d p'
  | stepDpChoiceR : forall (p1 p2 p' : ProcTerm) (d : DiscAct),
    stepDiscProc p2 d p' -> stepDiscProc (p1 $+$ p2) d p'
  | stepDpParL : forall (p p' q : ProcTerm) (d : DiscAct),
    stepDiscProc p d p' -> stepDiscProc (parComp p q) d (parComp p' q)
  | stepDpParR : forall (q q' p : ProcTerm) (d : DiscAct),
    stepDiscProc q d q' -> stepDiscProc (parComp p q) d (parComp p q')
  | stepDpSyncLR : forall (p p' q q' : ProcTerm) (c : Channel) (l : list BaseType),
    stepDiscProc p (outAct c l) p' -> stepDiscProc q (inAct c l) q' ->
    stepDiscProc (parComp p q) tauAct (parComp p' q')
  | stepDpSyncRL : forall (p p' q q' : ProcTerm) (c : Channel) (l : list BaseType),
    stepDiscProc p (inAct c l) p' -> stepDiscProc q (outAct c l) q' ->
    stepDiscProc (parComp p q) tauAct (parComp p' q')
  | stepDpApp : forall (n : Name) (l1 : list Var) (l2 : list Exp) (p p' : ProcTerm) (d : DiscAct),
    def n = pair l1 p -> stepDiscProc (subProcTerm (listsToSub l1 l2) p) d p' ->
    stepDiscProc (app n l2) d p'
  | stepDpTimeOut : forall (p p' : ProcTerm) (d : DiscAct) (e : Exp),
    stepDiscProc p d p' -> evalExpFunTime e = Some zeroTime -> stepDiscProc (del e p) d p'.




























(*******************Sort Relations******************)
(**Here is some machinery that will lay the groundwork for the delay semantics and also for
certain language properties.*)


(**For every delay d and term t, approximates whether or not the action a can be performed
within (but not including) d units of time by a derivative of t.*)
Inductive sort : DiscAct -> Delay -> ProcTerm -> Prop :=
  | sortOut : forall (c : Channel) (l1 : list Exp) (l2 : list BaseType)
    (p : ProcTerm) (d : Delay),
    evalExpLists l1 l2 -> sort (outAct c l2) d (outPrefix c l1 p)
  | sortIn : forall (c : Channel) (l1 : list Var) (l2 : list BaseType)
    (p : ProcTerm) (d : Delay), typedVals l1 l2 ->
    sort (inAct c l2) d (inPrefix c l1 p)
  | sortThen : forall (p : ProcTerm) (b : BoolExp) (a : DiscAct) (d : Delay),
    evalBoolExp b true -> sort a d p -> sort a d (ifThen b p)
  | sortSumL : forall (p1 p2 : ProcTerm) (a : DiscAct) (d : Delay),
    sort a d p1 -> sort a d (sum p1 p2)
  | sortSumR : forall (p1 p2 : ProcTerm) (a : DiscAct) (d : Delay),
    sort a d p2 -> sort a d (sum p1 p2)
  | sortParCompL : forall (p1 p2 : ProcTerm) (a : DiscAct) (d : Delay),
    sort a d p1 -> sort a d (parComp p1 p2)
  | sortParCompR : forall (p1 p2 : ProcTerm) (a : DiscAct) (d : Delay),
    sort a d p2 -> sort a d (parComp p1 p2)
  | sortApp : forall (p : ProcTerm) (a : DiscAct) (d : Delay)
    (n : Name) (l1 : list Var) (l2 : list Exp),
    def n = pair l1 p -> sort a d (subProcTerm (listsToSub l1 l2) p) -> sort a d (app n l2)
  | sortDel : forall (e : Exp) (t : Time) (d : Delay) (p : ProcTerm) (a : DiscAct),
    evalExpFunTime e = Some t -> sort a d p -> sort a (addDelayTime t d) (del e p).


(**A process p is discrete action enabled for the discrete action a iff
there is some process p' such that p transitions to p' via a.*)
Inductive discActEnabled (p : ProcTerm) (a : DiscAct) : Prop :=
  dae : forall p' : ProcTerm, stepDiscProc p a p' -> discActEnabled p a.

Open Scope R_scope.

(*******************Delay Semantics******************)

(**The timed action semantics over processes.*)
Inductive stepTimedProc : ProcTerm -> Delay -> ProcTerm -> Prop :=
  | stepTpNil : forall d : Delay, stepTimedProc nilProc d nilProc
  | stepTpOut : forall (d : Delay) (c : Channel) (l : list Exp) (p : ProcTerm),
    stepTimedProc (outPrefix c l p) d (outPrefix c l p)
  | stepTpIn : forall (d : Delay) (c : Channel) (l : list Var) (p : ProcTerm),
    stepTimedProc (inPrefix c l p) d (inPrefix c l p)
  | stepTpIfTrue : forall (p p' : ProcTerm) (d : Delay) (b : BoolExp),
    stepTimedProc p d p' -> evalBoolExpFunTot b  = true ->
    stepTimedProc (ifThen b p) d p'
  | stepTpIfFalse : forall (p : ProcTerm) (d : Delay) (b : BoolExp),
    evalBoolExpFunTot b = false -> stepTimedProc (ifThen b p) d (ifThen b p)
  | stepTpSum : forall (p1 p2 p1' p2' : ProcTerm) (d : Delay),
    stepTimedProc p1 d p1' -> stepTimedProc p2 d p2' ->
    stepTimedProc (sum p1 p2) d (sum p1' p2')
  (** For this law we need to assert that for all actions a that can be done by
    p within d units of time, the complementary action cannot be performed by q
    within that time.*)
  | stepTpPar : forall (p q p' q': ProcTerm) (d : Delay),
    stepTimedProc p d p' -> stepTimedProc q d q' ->
    (forall a : DiscAct, sort a d p -> ~sort (a^) d q) ->
    stepTimedProc (parComp p q) d (parComp p' q')
  | stepTpApp : forall (n : Name) (l1 : list Var) (l2 : list Exp) (p p' : ProcTerm) (d : Delay),
    def n = pair l1 p -> stepTimedProc (subProcTerm (listsToSub l1 l2) p) d p' ->
    stepTimedProc (app n l2) d p'
  | stepTpDelAdd : forall (p p' : ProcTerm) (d : Delay) (e : Exp) (t : Time),
    stepTimedProc p d p' -> evalExpFunTime e = Some t ->
    stepTimedProc (del e p) (t +dt+ d) p'
  | stepTpDelSub : forall (p : ProcTerm) (d : Delay) (e : Exp) (t : Time)
    (H : d <= t), evalExpFunTime e = Some t ->
    stepTimedProc (del e p) d (del (minusTime t d H) p)
  (** If the guard is ill formed, we just let the process idle.*)
  | stepTpDelIll : forall (p : ProcTerm) (d : Delay) (e : Exp),
    evalExpFunTime e = None -> stepTimedProc (del e p) d (del e p).

(**The mixture between the discrete and timed action semantics.*)
Inductive stepProc (t : ProcTerm) : Act -> ProcTerm -> Prop :=
  | stepPDisc : forall (a : DiscAct) (t' : ProcTerm),
    stepDiscProc t a t' -> stepProc t a t'
  | stepPTimed : forall (d : Delay) (t' : ProcTerm),
    stepTimedProc t d t' -> stepProc t d t'.

(** Returns p [x -> l] where def h = x, p.*)
Definition unfoldApp (h : Name) (l : list Exp) :=
  let (x, p) := def h in (subProcTerm (listsToSub x l) p).

(**The names applied in a term outside any input or output prefix. Unfolding a term
reaches these names without first doing an action.*)
Fixpoint unguardedNames (t : ProcTerm) : list Name :=
  match t with
  | nilProc => []
  | outPrefix _ _ _ => []
  | inPrefix _ _ _ => []
  | ifThen _ t' => unguardedNames t'
  | sum t1 t2 => unguardedNames t1 ++ unguardedNames t2
  | parComp t1 t2 => unguardedNames t1 ++ unguardedNames t2
  | app n _ => [n]
  | del _ t' => unguardedNames t'
  end.

End Semantics.

Open Scope R_scope.

Notation "p1 -PA- a -PA> p2" := (stepDiscProc p1 a p2) (left associativity, at level 50).
Notation "p1 -PD- d -PD> p2" := (stepTimedProc p1 d p2) (left associativity, at level 50).
Notation "p1 -P- a -P> p2" := (stepProc p1 a p2) (left associativity, at level 50).

(**The definitions are guarded: every cycle of names calling each other passes through an
input or output prefix. Equivalently, the names can be ranked so that a definition only
calls lower-ranked names outside a prefix. This generalises the guardedness of Remark 4.2
in the thesis, which asks that every name in a definition sit under a prefix.*)
Class GuardedDefs {PNames : ProcNames} {PDefs : ProcDefs} := {
  rank : Name -> nat;
  rank_unguarded : forall h h', In h' (unguardedNames (snd (def h))) ->
    (rank h' < rank h)%nat }.

Reserved Notation "t %; p" (at level 50).

(** Splits every hypothesis that a property holds along an appended list.*)
Local Ltac Forall_app_split := repeat match goal with
  [H : Forall _ (_ ++ _) |- _] => apply Forall_app in H; destruct H end.

Section Results.
Context {PNames : ProcNames} {PDefs : ProcDefs} {PGuarded : GuardedDefs}.

Open Scope R_scope.

(** Two processes are related if either they are equal or if there is a transition
linking them.*)
Inductive stepProcRefl : ProcTerm -> ProcTerm -> Prop :=
  | stprRefl : forall p : ProcTerm, stepProcRefl p p
  | stprTrans : forall (p1 p2 : ProcTerm) (a : Act),
    p1 -P- a -P> p2 -> stepProcRefl p1 p2.

Notation "p1 -P=> p2" := (stepProcRefl p1 p2) (at level 50).

(**A process p is timed action enabled for the delay d iff
there is some process p' such that p transitions to p' via d.*)
Inductive timedActEnabled (p : ProcTerm) (d : Delay) : Prop :=
  tae : forall p' : ProcTerm, stepTimedProc p d p' -> timedActEnabled p d.


(*********Guarded definitions*********)

(** Substitution doesn't change which names a term applies outside a prefix.*)
Lemma unguardedNames_sub (s : Subst) (p : ProcTerm) :
  unguardedNames (subProcTerm s p) = unguardedNames p.
Proof.
  revert s. induction p; intro s; simpl;
    try rewrite IHp; try rewrite IHp1, IHp2; reflexivity.
Qed.

(** Unfolding an application gives the body of its definition, with the arguments
substituted for the parameters.*)
Lemma unfoldApp_body (h : Name) (l : list Exp) :
  unfoldApp h l = subProcTerm (listsToSub (fst (def h)) l) (snd (def h)).
Proof. unfold unfoldApp. destruct (def h). reflexivity. Qed.

(** The identity substitution leaves a process term unchanged.*)
Lemma subProc_id_eq p : subProcTerm idSubst p = p.
  induction p; try simpl; try rewrite resetPreservesId;
  try rewrite idSubBoolExp;
  try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
  try rewrite idSubList; try rewrite idSubExp; try reflexivity.
  Qed.

(** An application can do whatever the body of its definition can do, with the
arguments substituted for the parameters.*)
Lemma stepDpApp_alt : forall (n : Name) (l2 : list Exp) (p' : ProcTerm) (a : DiscAct),
  stepDiscProc (subProcTerm (listsToSub (fst (def n)) l2) (snd (def n))) a p' ->
  stepDiscProc (app n l2) a p'. intros. remember (def n). destruct p. eapply stepDpApp.
  rewrite <- Heqp. reflexivity. apply H. Qed.

(** Helper for guarded_rect: induction on a bound for the ranks of the names a term
applies outside a prefix, then on the term.*)
Local Lemma guarded_rect_aux (P : ProcTerm -> Type)
  (Hnil : P nilProc)
  (Hout : forall c l p, P (outPrefix c l p))
  (Hin : forall c l p, P (inPrefix c l p))
  (Hif : forall b p, P p -> P (ifThen b p))
  (Hsum : forall p q, P p -> P q -> P (sum p q))
  (Hpar : forall p q, P p -> P q -> P (parComp p q))
  (Happ : forall h l, P (unfoldApp h l) -> P (app h l))
  (Hdel : forall e p, P p -> P (del e p)) :
  forall n p, (forall h, In h (unguardedNames p) -> (rank h < n)%nat) -> P p.
Proof.
  induction n as [|n IHn]; intro p;
    induction p as [| | | b p IHp | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2 | h l | e p IHp];
    simpl; intro B; auto;
    try solve [apply Hsum || apply Hpar;
      [apply IHp1 | apply IHp2]; intros h I; apply B, in_or_app; auto].
  - exfalso. specialize (B h (or_introl eq_refl)). lia.
  - apply Happ, IHn. intros h' I. rewrite unfoldApp_body, unguardedNames_sub in I.
    apply rank_unguarded in I. specialize (B h (or_introl eq_refl)). lia.
Qed.

(** Induction over process terms that unfolds the applications outside a prefix. It
holds because the definitions are guarded, so such unfolding always stops.*)
Lemma guarded_rect (P : ProcTerm -> Type)
  (Hnil : P nilProc)
  (Hout : forall c l p, P (outPrefix c l p))
  (Hin : forall c l p, P (inPrefix c l p))
  (Hif : forall b p, P p -> P (ifThen b p))
  (Hsum : forall p q, P p -> P q -> P (sum p q))
  (Hpar : forall p q, P p -> P q -> P (parComp p q))
  (Happ : forall h l, P (unfoldApp h l) -> P (app h l))
  (Hdel : forall e p, P p -> P (del e p)) :
  forall p, P p.
Proof.
  intro p. apply (guarded_rect_aux P Hnil Hout Hin Hif Hsum Hpar Happ Hdel
    (S (list_max (map rank (unguardedNames p))))).
  intros h I. assert (M : Forall (fun k => (k <= list_max (map rank (unguardedNames p)))%nat)
    (map rank (unguardedNames p))) by (apply list_max_le; lia).
  rewrite Forall_forall in M. specialize (M (rank h) (in_map rank _ _ I)). lia.
Qed.


(*********Results*********)

(*********Act Enabled "constructor" functions.*********)


(** If the left component of a sum is dae, then so is the entire sum.*)
Lemma daeSumL : forall (a : DiscAct) (p1 p2 : ProcTerm),
  discActEnabled p1 a -> discActEnabled (p1 $+$ p2) a. intros.
  invertClear H. eapply dae. constructor. apply H0. Qed.

(** If the right component of a sum is dae, then so is the entire sum.*)
Lemma daeSumR : forall (a : DiscAct) (p1 p2 : ProcTerm),
  discActEnabled p2 a -> discActEnabled (p1 $+$ p2) a. intros.
  invertClear H. eapply dae. apply stepDpChoiceR. apply H0. Qed.

(** An output prefix is enabled on its channel for the values its expressions evaluate to.*)
Lemma dae_outPfx c l v p :
  evalExpLists l v -> discActEnabled (c $<l>$! p) (c;! v). intro X.
  econstructor. constructor. assumption. Qed.

(** An input prefix is enabled on its channel for any values typed for its variables.*)
Lemma dae_inPfx c l v p :
  typedVals l v -> discActEnabled (c $<l>$? p) (c;? v).
  intro W. econstructor. constructor. assumption. Qed.

(** If the left component of a sum is dae, then so is the entire sum.*)
Lemma daeParL : forall (a : DiscAct) (p1 p2 : ProcTerm),
  discActEnabled p1 a -> discActEnabled (p1 $||$ p2) a. intros.
  invertClear H. eapply dae. constructor. apply H0. Qed.

(** If the right component of a sum is dae, then so is the entire sum.*)
Lemma daeParR : forall (a : DiscAct) (p1 p2 : ProcTerm),
  discActEnabled p2 a -> discActEnabled (p1 $||$ p2) a. intros.
  invertClear H. eapply dae. apply stepDpParR. apply H0. Qed.

(** If the body of a process definition is discActEnabled, then so is the application.*)
Lemma daeApp : forall (a : DiscAct) (x : list Var) (l : list Exp)
  (h : Name) (p : ProcTerm), def h = (x, p) ->
  discActEnabled (subProcTerm (listsToSub x l) p) a ->
  discActEnabled (h $(l)$) a. intros. invertClear H0.
  eapply dae. eapply stepDpApp. apply H. apply H1. Qed.

(** More cumbersome version but it fills in the variable list x and the process p automatically by
extracting them from the process definition of p.*)
Lemma daeAppAuto : forall (a : DiscAct) (l : list Exp) (h : Name),
  discActEnabled (subProcTerm (listsToSub (fst (def h)) l) (snd (def h))) a ->
  discActEnabled (h $(l)$) a. intros. remember (def h) as e. destruct e.
  symmetry in Heqe. eapply daeApp. apply Heqe. assumption. Qed.

(** If the then branch of an ifThen construct is discActEnabled for an action a,
and the guard evaluates to true, then the whole construct is dae by action a.*)
Theorem daeThenBranch : forall (a : DiscAct) (b : BoolExp) (p : ProcTerm),
  evalBoolExp b true -> discActEnabled p a -> discActEnabled (b $> p) a. intros.
  invertClear H0. eapply dae. constructor. apply H1. unfold evalBoolExpFunTot.
  apply evalBoolExpRelFun in H. rewrite H. reflexivity. Qed.

(** If p is discActEnabled for an action a, and the guard times out,
then the whole construct is dae by action a.*)
Theorem daeTimeout : forall (a : DiscAct) (e : Exp) (p : ProcTerm),
  evalExpFunTime e = Some zeroTime -> discActEnabled p a ->
  discActEnabled ($<e>$ p) a. intros. invertClear H0. eapply dae.
  constructor. apply H1. assumption. Qed.

(** All input prefixed terms are timed action enabled on all times.*)
Lemma taeIn : forall (d : Delay) (c : Channel) (l : list Var) (p : ProcTerm),
  timedActEnabled (c $<l>$ ? p) d. intros. eapply tae. constructor. Qed.

(** All output prefixed terms are timed action enabled on all times.*)
Lemma taeOut : forall (d : Delay) (c : Channel) (l : list Exp) (p : ProcTerm),
  timedActEnabled (c $<l>$ ! p) d. intros. eapply tae. constructor. Qed.

(** If both components of a sum are timedActEnabled, then so is the whole sum.*)
Lemma taeSum : forall (d : Delay) (p1 p2 : ProcTerm),
  timedActEnabled p1 d -> timedActEnabled p2 d ->
  timedActEnabled (p1 $+$ p2) d. intros.
  invertClear H. invertClear H0. eapply tae. constructor. apply H1.
  apply H. Qed.

(** If the body of a process definition is timedActEnabled, then so is the application.*)
Lemma taeApp : forall (d : Delay) (x : list Var) (l : list Exp)
  (h : Name) (p : ProcTerm), def h = (x, p) ->
  timedActEnabled (subProcTerm (listsToSub x l) p) d ->
  timedActEnabled (h $(l)$) d. intros. invertClear H0.
  eapply tae. eapply stepTpApp. apply H. apply H1. Qed.

(** More cumbersome version but it fills in the variable list x and the process p automatically by
extracting them from the process definition of p.*)
Lemma taeAppAuto : forall (d : Delay) (l : list Exp) (h : Name),
  timedActEnabled (subProcTerm (listsToSub (fst (def h)) l) (snd (def h))) d ->
  timedActEnabled (h $(l)$) d. intros. remember (def h) as e. destruct e.
  symmetry in Heqe. eapply taeApp. apply Heqe. assumption. Qed.

(** If the then branch of an ifThen construct is timedActEnabled for an amount d,
then the whole construct can delay by this amount.*)
Theorem taeThenBranch : forall (d : Delay) (b : BoolExp) (p : ProcTerm),
  timedActEnabled p d -> timedActEnabled (b $> p) d. intros.
  remember (evalBoolExpFunTot b). invertClear H. destruct b0; eapply tae.
  constructor. apply H0. symmetry. assumption. apply stepTpIfFalse.
  symmetry. assumption. Qed.


(*********Some things about sort.*********)

(** If a process p is guarded by a value that is timed out, then all actions available
to p within d are available to the guarded p within that time d.*)
Lemma sortTimeOut : forall (e : Exp) (d : Delay) (p : ProcTerm) (a : DiscAct),
  evalExpFunTime e = Some zeroTime -> sort a d p -> sort a d (del e p).
  intros. rewrite <- (timeDelAddZeroL d). constructor; assumption. Qed.

(** If a process is enabled on a discrete action a other than tau,
then forall delays d, a is in sort d for that process.*)
Lemma enabledInSort : forall (a : DiscAct) (d : Delay) (p : ProcTerm),
  discActEnabled p a -> a <> tauAct -> sort a d p.
  intros. inversion H. induction H1; try solve [apply False_ind; apply H0;
  reflexivity]. constructor; assumption. constructor.
  assumption. constructor. rewrite evalBoolExpTrueTot. assumption.
  apply IHstepDiscProc. inversion H. inversion H3. eapply dae.
  apply H6. assumption. constructor. apply IHstepDiscProc.
  eapply dae. apply H1. assumption. apply sortSumR.
  apply IHstepDiscProc. eapply dae. apply H1. assumption.
  constructor. apply IHstepDiscProc. eapply dae. apply H1.
  assumption. apply sortParCompR. apply IHstepDiscProc. eapply dae.
  apply H1. assumption. eapply sortApp. apply H1.
  apply IHstepDiscProc. eapply dae. inversion H.
  inversion H3. rewrite H6 in H1. inversion H1. apply H2.
  assumption. eapply sortTimeOut. assumption. apply IHstepDiscProc.
  inversion H. inversion H3. eapply dae. apply H6. assumption. Qed.

Lemma enabledInSort_in (c : Channel) (v : list BaseType) (d : Delay) (p : ProcTerm) :
  discActEnabled p (c ;? v) -> sort (c ;? v) d p. intros. eapply enabledInSort.
  assumption. unfold not. intro. inversion H0. Qed.

Lemma enabledInSort_out (c : Channel) (v : list BaseType) (d : Delay) (p : ProcTerm) :
  discActEnabled p (c ;!v) -> sort (c ;! v) d p. intros. eapply enabledInSort.
  assumption. unfold not. intro. inversion H0. Qed.

(** If we can prove sort a d p, then the action a is either an input of some vector
or the output of some vector.*)
Lemma sortInOrOut : forall (a : DiscAct) (d : Delay) (p : ProcTerm),
  sort a d p -> exists v : list BaseType, exists c : Channel,
  a = c ;? v \/ a = c ;! v. intros. induction H; try apply IHsort.
  exists l2. exists c. right. reflexivity. exists l2. exists c. left.
  reflexivity. Qed. 
  
(** If an action is in sort d of p, then it is also in sort d + d' of p.*)
Theorem sortAddR : forall (a : DiscAct) (d d' : Delay) (p : ProcTerm),
  sort a d p -> sort a (d +d+ d') p. intros. induction H;
  try solve [constructor; assumption]. 
  eapply sortApp. apply H. assumption.
  rewrite delTimeAddAssoc2. constructor; assumption. Qed.

(** If an action is in sort d of p, then it is also in sort d' + d of p.*)
Theorem sortAddL : forall (a : DiscAct) (d d' : Delay) (p : ProcTerm),
  sort a d p -> sort a (d' +d+ d) p. intros. rewrite addDelayComm.
  apply sortAddR. assumption. Qed.

(** If an action is in sort d of p, then it is also in sort t + d of p.*)
Theorem sortAddTime : forall (a : DiscAct) (d : Delay) (t : Time) (p : ProcTerm),
  sort a d p -> sort a (t +dt+ d) p. intros. induction H;
  try solve [constructor; assumption]. 
  eapply sortApp. apply H. assumption.
  rewrite timeDelAddComm. constructor; assumption. Qed.

(** If sort a d p and d' <= d, then sort a d' p.*)
Theorem sortLe : forall (a : DiscAct) (d d' : Delay) (p : ProcTerm),
  sort a d p -> d <= d' -> sort a d' p. intros. apply RlePlusExistsL in H0.
  invertClear H0. invertClear H1. remember (mkTime (mknonnegreal x H2)) as t.
  assert (d' = t +dt+ d). rewrite Heqt. apply delayEqR. apply H0.
  rewrite H1. apply sortAddTime. assumption. Qed.

Ltac evalExp_evalExpFunTime_step := match goal with
  [V : ?e |_| baseTime ?t |- _] => apply evalExp_evalExpFunTime in V end.

(** If a is in sort d' of p' and p transitions to p' by d, then a is in the sort
d + d' of p.*)
(* begin helpers for sortDeriv *)
(** Helper for sortDeriv: the case of a guard that has been partially counted down.*)
Lemma sortDeriv_aux (a : DiscAct) (d d' : Delay) (t : Time) (H : d <= t) e p :
  evalExpFunTime e = Some t ->
  sort a d' ($< minusTime t d H >$ p) -> sort a (d +d+ d') ($< e >$ p).
  intros EV S. inversion S; subst. simpl in H4. injection H4. intro EQ.
  replace (d +d+ (t0 +dt+ d0)) with (t +dt+ d0).
  constructor; assumption. apply delayEqR. subst. simpl. ring. Qed.
(* end helpers *)

Theorem sortDeriv : forall (a : DiscAct) (d d' : Delay) (p p' : ProcTerm),
  sort a d' p' -> p -PD- d -PD> p' -> sort a (d +d+ d') p.
Proof.
 intros.
  induction H0; try solve [inversion H; constructor; assumption].
  apply IHstepTimedProc in H. constructor. rewrite evalBoolExpTrueTot.
  assumption. assumption. inversion H. rewrite evalBoolExpTrueTot in H5.
  rewrite H0 in H5. inversion H5. inversion H. apply IHstepTimedProc1 in H3.
  constructor. assumption. apply IHstepTimedProc2 in H3. apply sortSumR.
  assumption. inversion H. apply IHstepTimedProc1 in H4.
  constructor. assumption. apply IHstepTimedProc2 in H4. apply sortParCompR.
  assumption. apply IHstepTimedProc in H. eapply sortApp. apply H0.
  assumption. apply IHstepTimedProc in H. rewrite delTimeAddAssoc2.
  constructor; assumption.
  eapply sortDeriv_aux; eassumption.
  inversion H. rewrite H0 in H5. inversion H5.
  (*Not sure what happened here - proof seems to have got corrupted:
  eapply sort_guard_eval_eq. apply H. rewrite H1.
  apply evalExpFunTime_time.
  inversion H. rewrite H0 in H5. inversion H5. Qed.*)
  Qed.

Lemma sort_minus_guard a d' d t H p :
  sort a d' ($<eBase (baseTime (minusTime (nonneg (time t))
  (pos (delay d)) H))>$ p) ->
  sort a (d +d+ d') ($<eBase (baseTime t)>$ p).
Proof.
  apply sortDeriv_aux. destruct t. reflexivity. Qed.

Lemma evalExpFunTime_time t :
  evalExpFunTime (eBase (baseTime t)) = Some t.
  destruct t. unfold evalExpFunTime. simpl. reflexivity.
  Qed.

(** A time that evaluates to the zero time is zero.*)
Lemma evalExpFunTime_zero_inv t :
  evalExpFunTime (liftTimeExp t) = Some zeroTime -> nonneg (time t) = 0.
Proof.
  unfold liftTimeExp. rewrite evalExpFunTime_time. intro E. injection E as E. subst.
  reflexivity.
Qed.

Lemma sort_guard_eval_eq a d e1 e2 p :
  sort a d ($<e1>$ p) ->
  evalExpFunTime e1 = evalExpFunTime e2 ->
  sort a d ($<e2>$ p). intros. inversion H.
  rewrite H0 in H5. constructor; assumption. Qed.

(** A version of sortDeriv but as an equivalence rather than an implication.*)
Corollary sortDerivEquiv (a : DiscAct) (d d' : Delay) (p p' : ProcTerm) :
  p -PD- d -PD> p' -> (sort a d' p' <-> sort a (d +d+ d') p). intros.
  split. intros. eapply sortDeriv. apply H0. assumption.
  induction H; intro; try solve [inversion H; constructor; assumption].
  inversion H1. apply IHstepTimedProc. assumption.
  inversion H0. rewrite evalBoolExpTrueTot in H5. rewrite H in H5. inversion H5.
  inversion H1. constructor. apply IHstepTimedProc1. assumption.
  apply sortSumR. apply IHstepTimedProc2. assumption.
  inversion H2. constructor. apply IHstepTimedProc1. assumption.
  apply sortParCompR. apply IHstepTimedProc2. assumption.
  apply IHstepTimedProc. inversion H1. rewrite H in H6. inversion H6. assumption.
  inversion H1. apply IHstepTimedProc. eapply sortLe. apply H7.
  replace (pos (delay d0)) with (d + d'). apply Rle_refl.
  symmetry. cut (nonneg (time t) + pos (delay d0) =
  nonneg (time t) + pos (delay d) + pos (delay d')). intro.
  eapply Rplus_eq_reg_l. rewrite Rplus_assoc in H8. apply H8.
  replace t0 with t in H2. apply H2. cut ((baseTime t) = (baseTime t0)).
  intro. inversion H8. reflexivity.
  rewrite H0 in H6. inversion H6. reflexivity.
  invertClear H1. assert (t = t0). cut ((baseTime t) = (baseTime t0)).
  intro. inversion H1. reflexivity.
  rewrite H0 in H6. inversion H6.
  reflexivity.
  subst. clear H0. cut (d' = minusTime t0 d H +dt+ d0). intros. rewrite H0.
  constructor. constructor. assumption. apply delayEqR.
  apply Rplus_eq_reg_l with (r := d). destruct t0, d0, d, d'.
  destruct time, delay, delay0, delay1. simpl. simpl in H2.
  symmetry in H2. rewrite H2. ring. inversion H0. rewrite H in H5.
  inversion H5.
  Qed.


Import ComhCoq.lib.Extras.LibTactics.
Open Scope R_scope.

(**Sort captures at least all the actions that are available within the delay d. The converse
of this theorem is not true: sort does over-approximate.*)
Theorem sort_complete d a p :
  a <> tauAct /\ (discActEnabled p a \/
  exists d' p', delay d' < delay d /\ p -PD- d' -PD> p' /\ discActEnabled p' a)
  -> sort a d p. introz U.
  (*Action implies sort*)
  andflat L. elimOr2 L0 Q. apply enabledInSort; assumption.
  rename Q into U. decompEx2 U d' p' LD.
  andflat U. Rlttoplus U x RL. mkdel x RL0 d''.
  lets ES : (enabledInSort a d'') U2 L. assert (d = d' +d+ d'').
  apply delayEqR. rewrite Heqd''. simpl. rewrite Rplus_comm. assumption.
  rewrite H. eapply sortDeriv. apply enabledInSort. apply U2. assumption.
  assumption. Qed.

(*********Misc.*********)

(** If a parallel construct delays to another process then the resulting process is
itself a parallel construct, whose terms either match the original or are related
to the original via a single transition.*)
Theorem parStructPres : forall (p1 p2 p' : ProcTerm) (a : Act),
  p1 $||$ p2 -P- a -P> p' -> exists p1', exists p2',
  p' = p1' $||$ p2' /\ p1 -P=> p1' /\ p2 -P=> p2'. intros.
  destruct p'; inversion H; inversion H0; exists p'1;
  exists p'2; (split; [reflexivity | ]).
  split; [eapply stprTrans; apply stepPDisc; apply H6 | eapply stprRefl].
  split; [eapply stprRefl |eapply stprTrans; apply stepPDisc; apply H6 ].
  split; eapply stprTrans; apply stepPDisc. apply H7. apply H9.
  split; eapply stprTrans; apply stepPDisc. apply H7. apply H9.
  split; eapply stprTrans; apply stepPTimed. apply H8. apply H9.
  Qed.

(** Parallel structural preservation for the reflexive transition relation.*)
Theorem parStructPres2 : forall (p1 p2 p' : ProcTerm),
  p1 $||$ p2 -P=> p' -> exists p1', exists p2',
  p' = p1' $||$ p2' /\ p1 -P=> p1' /\ p2 -P=> p2'. intros.
  inversion H. exists p1. exists p2. split. reflexivity.
  split; constructor. eapply parStructPres. apply H0. Qed.
















(*********Seemingly big language results, and other rubbish.*********)

(** Whenever a process p can do a silent action, it cannot do a delay.*)
Theorem maximalProgressProc : forall (p : ProcTerm) (d : Delay),
  discActEnabled p tauAct -> ~timedActEnabled p d. intros.
  remember tauAct as a. invertClear H. generalize dependent d.
  induction H0; unfold not; intros; try (apply (IHstepDiscProc Heqa d0));
  try inversion H1; try inversion H2. inversion Heqa. inversion Heqa.
  eapply tae. apply H5. apply False_ind. cut (true = false). intros.
  inversion H8. eapply evalBoolExpUnique. rewrite evalBoolExpTrueTot.
  apply H. inversion H. inversion H1. rewrite H7 in H9. inversion H9.
  inversion H. inversion H1. eapply tae. apply H4.
  inversion H. inversion H1. eapply tae. apply H7.
  inversion H. inversion H1. eapply tae. apply H4.
  inversion H. inversion H1. eapply tae. apply H5.
  inversion H. inversion H0. eapply H7.
  cut (sort (c ;! l) d p). intros. apply H8. apply enabledInSort.
  eapply dae. apply H0_. unfold not. intros. inversion H8.
  apply enabledInSort. eapply dae. apply H0_0. unfold not. intros.
  inversion H8. inversion H. inversion H0. eapply H7.
  cut (sort (c ;? l) d p). intros. apply H8. apply enabledInSort.
  eapply dae. apply H0_. unfold not. intros. inversion H8.
  apply enabledInSort. eapply dae. apply H0_0. unfold not. intros.
  inversion H8. invertClear H1. invertClear H2. rewrite H5 in H.
  invertClear H. rewrite H15 in H8. eapply tae. rewrite <- H16.
  apply H8. apply False_ind. apply (IHstepDiscProc Heqa d1).
  eapply tae. apply H5.
  (** In this case, we show a contradiction because the guard is assumed both
  to be greater than the delay d and also to have timed out to 0.*)
  assert (baseTime t = baseTime zeroTime).
  rewrite H in H8. inversion H8. reflexivity.
  apply False_ind.
  apply (Rlt_irrefl zeroTime). inversion H9. clear H7.
  rewrite H11 in H3. apply Rlt_le_trans with (r2 := d0).
  apply cond_pos. assumption.
  (** Contradiction: Guard timed out but also ill formed.*)
  rewrite H in H7. inversion H7. Qed.

(** If a process p can delay by d'' to become p'', and there is some d, d' such
that d'' = d + d', then there is some p' such that p can delay by d to get to p',
and p' can delay by d' to p''.*)
Theorem timeSplit : forall (p p'' : ProcTerm) (d d' d'' : Delay),
  p -PD- d'' -PD> p'' -> d'' = d +d+ d' -> exists p',
  p -PD- d -PD> p' /\ p' -PD- d' -PD> p''. intros.
  generalize dependent d'. generalize dependent d. induction H; intros.
  exists nilProc. split; constructor. exists (c $< l >$ !p).
  split; constructor. exists (c $< l >$ ? p). split; constructor.
  apply (IHstepTimedProc d0 d') in H1. invertClear H1. exists x.
  invertClear H2. split. constructor; assumption. assumption.
  exists (b $> p). split; apply stepTpIfFalse; assumption.
  addHyp (IHstepTimedProc1 d0 d' H1). addHyp (IHstepTimedProc2 d0 d' H1).
  invertClear H2. invertClear H3. invertClear H4. invertClear H2.
  exists (x $+$ x0). split; constructor; assumption.
  addHyp (IHstepTimedProc1 d0 d' H2). addHyp (IHstepTimedProc2 d0 d' H2).
  invertClear H3. invertClear H4. invertClear H5. invertClear H3.
  exists (x $||$ x0). split; constructor; try assumption.
  unfold not. intros. assert (sort a d p). rewrite H2. apply sortAddR.
  apply H3. apply H1 in H9. apply H9. rewrite H2. apply sortAddR. assumption.
  unfold not; intros. apply sortDeriv with (d := d0) (p := p) in H3.
  rewrite <- H2 in H3. apply H1 in H3. apply H3. rewrite H2. eapply sortDeriv.
  apply H8. assumption. assumption.
  addHyp (IHstepTimedProc d0 d' H1). invertClear H2. clear IHstepTimedProc.
  exists x. invertClear H3. split. eapply stepTpApp. apply H.
  assumption. assumption. addHyp (Rle_lt_dec d0 t). invertClear H2.
  (** Case d0 <= t, then we can proceed via del sub.*)
  exists ($< minusTime t d0 H3 >$ p). split. constructor. assumption.
  assert (d' = minusTime t d0 H3 +dt+ d). destruct d, d', t, d0.
  destruct delay, time, delay0. apply delayEqR. simpl. unfold addDelay in H1.
  unfold addDelayTime in H1. simpl in H1. inversion H1. symmetry in H4.
  replace pos0 with (delay1 + pos0 - delay1). replace (nonneg - delay1 + pos) with
  (nonneg + pos - delay1). f_equal. assumption. ring. ring. rewrite H2.
  constructor. assumption. constructor.
  (** Case t < d0, then we split the delay d into (d0 - t) and d', and we proceed
  via the induction hypothesis and delAdd.*)
  assert (d = (minusDelay d0 t H3) +d+ d'). destruct d, d0, t, d'.
  destruct delay, time, delay0, delay1. unfold addDelay in H1. simpl in H1.
  inversion H1. apply delayEqR. simpl. replace pos with (nonneg + pos - nonneg);
  try ring. replace (pos0 - nonneg + pos1) with (pos0 + pos1 - nonneg); try ring.
  f_equal. assumption. remember (minusDelay d0 t H3) as x.
  addHyp (IHstepTimedProc x d' H2). invertClear H4. exists x0.
  invertClear H5. assert (d0 = t +dt+ x). rewrite Heqx. apply minusDelayAddTime.
  rewrite H5. split. constructor; assumption. assumption.
  (** Now we do the case where the entire delay is less than the guard, in which case
  we can proceed via delSub twice.*)
  assert (d0 < t). apply Rlt_le_trans with (r2 := d). replace (pos d0) with (d0 + 0);
  [|ring]. rewrite H1. simpl. apply Rplus_le_lt_compat. apply Rle_refl. apply cond_pos.
  assumption. (*Now we have that d0 < t and can go ahead and insert the ex witness.*)
  apply Rlt_le in H2. exists ($< minusTime t d0 H2 >$ p).
  (*Now let's assert that d' is less than or equal t - d.*)
  assert (d' <= minusTime t d0 H2). assert (pos d' = d - d0). rewrite H1.
  simpl. ring. rewrite H3. simpl. apply Rplus_le_compat. assumption. apply Rle_refl.
  split. constructor. assumption.
  assert (minusTime t d H = (minusTime (minusTime t d0 H2) d' H3)).
  apply timeEqR. simpl. rewrite H1. simpl. ring. rewrite H4. constructor.
  constructor. exists ($< e >$ p). split; apply stepTpDelIll; assumption. Qed.

(** If p can delay by d, then p can delay by any d' strictly less than d.*)
Lemma delShortenStrict : forall (p : ProcTerm) (d d' : Delay),
  timedActEnabled p d -> d' < d -> timedActEnabled p d'.
  intros. apply RltPlusExistsR in H0.
  invertClear H0. invertClear H1. remember (mkDelay (mkposreal x H2)) as d''.
  assert (d = d' +d+ d''). apply addRaddDel. rewrite Heqd''. apply H0.
  invertClear H. addHyp (timeSplit p p' d' d'' d H3 H1). invertClear H.
  invertClear H4. eapply tae. apply H. Qed.

(** If p can delay by d, then p can delay by any d' less than or equal d.*)
Lemma delShorten : forall (p : ProcTerm) (d d' : Delay),
  timedActEnabled p d -> d' <= d -> timedActEnabled p d'. intros.
  apply Rle_lt_or_eq_dec in H0. invertClear H0. eapply delShortenStrict.
  apply H. assumption. assert (d' = d). apply delayEqR.
  assumption. rewrite H0. assumption. Qed.

Lemma taeSumEx (p1 p2 : ProcTerm) : (exists d, timedActEnabled p1 d) ->
  (exists d, timedActEnabled p2 d) -> exists d, timedActEnabled (p1 $+$ p2) d.
  intros. invertClear H. invertClear H0. addHyp (Rle_lt_dec x x0).
  invertClear H0. exists x. apply taeSum. assumption. eapply delShorten.
  apply H. assumption. apply (Rlt_le) in H2. exists x0. apply taeSum.
  eapply delShorten. apply H1. assumption. assumption. Qed.

(** If a process can delay to another process, then all discrete actions available
to the original process are available to the derivative.*)
Theorem persistence : forall (p p' : ProcTerm) (d : Delay) (a : DiscAct),
  p -PD- d -PD> p' -> discActEnabled p a -> discActEnabled p' a. intros.
  induction H; try assumption. invertClear H0; invertClear H2.
  assert (discActEnabled p a). eapply dae. apply H4. apply IHstepTimedProc.
  assumption. invertClear H0; invertClear H2.
  (*Case: Sum*)
  apply daeSumL. apply IHstepTimedProc1. eapply dae. apply H6.
  apply daeSumR. apply IHstepTimedProc2. eapply dae. apply H6.
  (*Case: Par normal*)
  invertClear H0; invertClear H3. apply daeParL. apply IHstepTimedProc1.
  eapply dae. apply H7. apply daeParR. apply IHstepTimedProc2. eapply dae. apply H7.
  (*Case: Par contradiction (handshake communiction happens)*)
  apply False_ind. assert (sort (c;! l) d p). apply enabledInSort.
  eapply dae. apply H5. unfold not. intros. inversion H3.
  assert (sort (c;? l) d q). apply enabledInSort.
  eapply dae. apply H8. unfold not. intros. inversion H9.
  apply (H2 (c;! l) H3). simpl. assumption.
  apply False_ind. assert (sort (c;! l) d q). apply enabledInSort.
  eapply dae. apply H8. unfold not. intros. inversion H3.
  assert (sort (c;? l) d p). apply enabledInSort.
  eapply dae. apply H5. unfold not. intros. inversion H9.
  apply (H2 (c;? l) H9). simpl. assumption.
  (*The rest of the cases*)
  invertClear H0. invertClear H2.
  assert (discActEnabled (subProcTerm (listsToSub l1 l2) p) a). eapply dae.
  rewrite H in H4. inversion H4. apply H7. apply IHstepTimedProc. assumption.
  apply IHstepTimedProc. inversion H0. inversion H2.
  eapply dae. apply H5. invertClear H0. invertClear H2.
  assert (baseTime t = zeroTime).
  rewrite H1 in H7. inversion H7. reflexivity. 
  invertClear H2. apply False_ind. rewrite H9 in H. eapply Rlt_not_le.
  apply (cond_pos d). apply H. Qed.

(** If a process p can delay by d'' to become p'', then there is some p', d, d' such
that d'' = d + d' and p can delay by d to get to p' and p' can delay by d' to p''.*)
Theorem timeSplitEx : forall (p p'' : ProcTerm) (d'' : Delay),
  p -PD- d'' -PD> p'' -> exists p', exists d, exists d',
  d'' = d +d+ d' /\ p -PD- d -PD> p' /\ p' -PD- d' -PD> p''. intros.
  addHyp (addDelayExists d''). invertClear H0. invertClear H1.
  rename x into d. rename x0 into d'. addHyp (timeSplit p p'' d d' d'' H H0).
  invertClear H1. exists x. exists d. exists d'. split; assumption.
  Qed.

(** If a guarded process can delay by d, and the guard evaluates to some t, then
the guarded construct can delay by that same d.*)
Lemma taeDelWf : forall (d : Delay) (e : Exp) (t : Time) (p : ProcTerm),
  evalExpFunTime e = Some t -> timedActEnabled p d -> timedActEnabled ($<e>$ p) d.
  intros. invertClear H0. addHyp (Rle_lt_dec d t).
  invertClear H0. apply tae with (p' := $< minusTime t d H2 >$ p).
  constructor. assumption. addHyp (minusDelayAddTime d t H2).
  rewrite H0. apply tae in H1.
  apply delShorten with (d' := minusDelay d t H2) in H1.
  invertClear H1. eapply tae. constructor. apply H3.
  assumption. cut (minusDelay d t H2 <= t +dt+ minusDelay d t H2).
  intros. rewrite <- H0 in H3. assumption. simpl. Rplus_le_tac.
  timeNonneg. Qed.

(** If the guarded process in a delay guard construct is enabled on d, then so is
the entire construct. We prove this by a case analysis on the well formedness of the
evaluation of the guard expression. If it is well formed, then it evaluates to some t,
and so we can apply taeDelWf. Otherwise, we can simply apply the constructor for ill
formed delay guarded processes.*)
Theorem taeDel : forall (d : Delay) (e : Exp) (p : ProcTerm),
  timedActEnabled p d -> timedActEnabled ($<e>$ p) d. intros.
  inversion H. remember (evalExpFunTime e) as v. destruct v. 
  symmetry in Heqv. lets LDT : (Rle_or_lt d t). or_flat.
  apply tae with (p' := ($< minusTime t d OR >$ p)).   
  constructor. assumption. apply RltPlusExistsR in OR0.
  ex_flat. and_flat. mkdel x AND0 d'. assert (d' <= d).
  rewrite AND. rewrite Heqd'. simpl. Rplus_le_tac.
  timeNonneg. eapply delShorten in H;[ | apply H1].
  inversion H. eapply tae. assert (d = t +dt+ d').
  apply delayEqR. rewrite Heqd'. simpl. apply AND.
  rewrite H3. eapply stepTpDelAdd. apply H2. assumption.
  econstructor. eapply stepTpDelIll. symmetry. assumption. Qed.

  



























(*********************Decidable Synch checking*******************************)
(*In this section we develop machinery towards the formulation of a decision
procedure for checking whether or not two processes can synchronise.
This is important for reasoning about parallel delays, which enforce a noSync
condition, that is necessary for maximal progress. Firstly, we define minguard,
which shows us that the sort relation is equivalent to the actions available now below
a certain threshold of delay. Hence we reduce the problem to ensuring that
the actions available now can't synchronise. Towards this end, we define machinery
that will calculate in a finite and somewhat symbolic way the input and output
actions available to a process.*)

(** minGuard t P roughly says that t is less than or equal to the smallest delay
guard encountered in an expansion of P- by expansion of P what is meant is a recursive
drilling into unguarded terms until the resulting process contains only guarded terms.*)
Inductive minGuard : Delay -> ProcTerm -> Prop :=
  | mgNil : forall (d : Delay), d %; nilProc
  | mgIn : forall (d : Delay) (p : ProcTerm) (c : Channel) (l : list Var), d %; (c $< l >$ ? p)
  | mgOut : forall (d : Delay) (p : ProcTerm) (c : Channel) (l : list Exp), d %; (c $< l >$ ! p)
  | mgIfTrue : forall (d : Delay) (p : ProcTerm) (b : BoolExp),
    d %; p -> evalBoolExp b true -> d %; (b $> p)
  | mgIfFalse :  forall (d : Delay) (p : ProcTerm) (b : BoolExp),
    evalBoolExpFunTot b = false -> d %; (b $> p)
  | mgSumL : forall (d1 d2 : Delay) (p q : ProcTerm),
    d1 %; p -> d2 %; q -> d1 <= d2 -> d1 %; (p $+$ q)
  | mgSumR : forall (d1 d2 : Delay) (p q : ProcTerm),
    d1 %; p -> d2 %; q -> d2 < d1 -> d2 %; (p $+$ q)
  | mgParL : forall (d1 d2 : Delay) (p q : ProcTerm),
    d1 %; p -> d2 %; q -> d1 <= d2 -> d1 %; (p $||$ q)
  | mgParR : forall (d1 d2 : Delay) (p q : ProcTerm),
    d1 %; p -> d2 %; q -> d2 < d1 -> d2 %; (p $||$ q)
  | mgApp : forall (d : Delay) (p : ProcTerm) (h : Name) (l1 : list Var) (l2 : list Exp),
    def h = pair l1 p -> d %; (subProcTerm (listsToSub l1 l2) p) -> d %; (h $(l2)$)
  | mgDelEval : forall (d : Delay) (t : Time) (p : ProcTerm) (e : Exp),
    evalExpFunTime e = Some t -> d <= t -> d %; ($< e >$ p)
  | mgDelIll : forall (d : Delay) (p : ProcTerm) (e : Exp),
    evalExpFunTime e = None -> d %; ($< e >$ p)
  | mgDelTimeout : forall (d : Delay) (p : ProcTerm) (e : Exp),
    evalExpFunTime e = Some zeroTime -> d %; p -> d %; ($< e >$ p)
  where "d %; p" := (minGuard d p).

(** If t2 is minGuard p, then all t1 <= t2 are also minGuard p. Follows by induction, the only
"interesting" case being mgDelEval, in which case we use the transitivity of the Rle relation to
prove this property.*)
Lemma minGuardLe : forall (d1 d2 : Delay) (p : ProcTerm),
  d2 %; p -> d1 <= d2 -> d1 %; p. intros. induction H; try solve [constructor; assumption].
  constructor. apply IHminGuard. assumption. assumption. 
  addHyp (IHminGuard1 H0). eapply mgSumL. assumption. apply H1. eapply Rle_trans.
  apply H0. assumption. addHyp (IHminGuard2 H0). eapply mgSumR. apply H.
  assumption. eapply Rle_lt_trans. apply H0. assumption.
  addHyp (IHminGuard1 H0). eapply mgParL. assumption. apply H1. eapply Rle_trans.
  apply H0. assumption. addHyp (IHminGuard2 H0). eapply mgParR. apply H.
  assumption. eapply Rle_lt_trans. apply H0. assumption.
  addHyp (IHminGuard H0). eapply mgApp. apply H. assumption.
  eapply mgDelEval. apply H. eapply Rle_trans. apply H0. assumption.
  apply IHminGuard in H0. apply mgDelTimeout; assumption. Qed.

(** If we can show that minGuard d p, then for all actions, sort a d p implies
p being able to actually perform the action a now.*)
Theorem sortMinGuard1 : forall (a : DiscAct) (d : Delay) (p : ProcTerm),
  d %; p -> sort a d p -> discActEnabled p a. intros. induction H0. eapply dae.
  constructor. assumption. eapply dae. constructor. assumption.
  inversion H. addHyp (IHsort H5). invertClear H7. eapply dae. constructor.
  apply H8. unfold evalBoolExpFunTot. apply evalBoolExpRelFun in H6. rewrite H6.
  reflexivity. unfold evalBoolExpFunTot in H4. apply evalBoolExpRelFun in H0.
  rewrite H0 in H4. inversion H4.
  (*Case : sort sum left*)
  invertClear H. addHyp (IHsort H3).
  invertClear H. eapply dae. constructor. apply H7. assert (d %; p1).
  eapply minGuardLe. apply H3. apply Rlt_le. assumption. addHyp (IHsort H).
  invertClear H7. eapply dae. constructor. apply H8.
  (*Case : sort sum right*)
  invertClear H. assert (d %; p2). eapply minGuardLe. apply H5.
  assumption. addHyp (IHsort H). invertClear H7. eapply dae.
  apply stepDpChoiceR. apply H8. addHyp (IHsort H5). invertClear H.
  eapply dae. apply stepDpChoiceR. apply H7.
  (*Case : sort par left*)
  invertClear H. addHyp (IHsort H3).
  invertClear H. eapply dae. constructor. apply H7. assert (d %; p1).
  eapply minGuardLe. apply H3. apply Rlt_le. assumption. addHyp (IHsort H).
  invertClear H7. eapply dae. constructor. apply H8.
  (*Case : sort par right*)
  invertClear H. assert (d %; p2). eapply minGuardLe. apply H5.
  assumption. addHyp (IHsort H). invertClear H7. eapply dae.
  apply stepDpParR. apply H8. addHyp (IHsort H5). invertClear H.
  eapply dae. apply stepDpParR. apply H7. 
  (*Case : app*)
  invertClear H. rewrite H0 in H5. inversion H5. subst. addHyp (IHsort H6).
  invertClear H. eapply dae. eapply stepDpApp. apply H0. apply H2.
  (*Case : del guard. First 2 cases contradiction, 3rd case provable.*)
  inversion H. cut (t = t0). intro. rewrite H7 in H6. simpl in H6.
  apply Rplus_le_swap_ll in H6. apply Rle_not_lt in H6. false.
  apply H6. Rminus_refl_simpl. delPos. rewrite H0 in H5. inversion H5.
  reflexivity.
  (*Sub-case 2*)
  rewrite H0 in H4. inversion H4.
  (*Sub-case 3*)
  assert (t = zeroTime). rewrite H0 in H5. inversion H5. reflexivity.
  rewrite H7 in H6. assert (d %; p). my_applys_eq H6. apply delayEqR.
  simpl. ring. apply IHsort in H8. inversion H8. do 2 econstructor;
  eassumption. Qed.
  

(** If we can show that minGuard d p, then for all actions, sort a d p is equivalent to
p being able to actually perform the action a now.*)
Theorem sortMinGuard2 : forall (a : DiscAct) (d : Delay) (p : ProcTerm),
  d %; p -> a <> tauAct -> (sort a d p <-> discActEnabled p a). split.
  apply sortMinGuard1. assumption. intros. apply enabledInSort; assumption. Qed.

(** All input prefixed terms are minGuarded by any delay.*)
Lemma mgInEx : forall (c : Channel) (l : list Var) (p : ProcTerm),
  exists d, d %; (c $<l>$ ? p). intros. exists (mkDelay onePos).
  constructor. Qed.

(** All output prefixed terms are minGuarded by any delay.*)
Lemma mgOutEx : forall (c : Channel) (l : list Exp) (p : ProcTerm),
  exists d, d %; (c $<l>$ ! p). intros. exists (mkDelay onePos).
  constructor. Qed.


(** If both components of a sum are have some minGuard, then so does the whole sum.*)
Lemma mgSumEx : forall (p1 p2 : ProcTerm),
  (exists d1, d1 %; p1) -> (exists d2, d2 %; p2) ->
  exists d, d %; (p1 $+$ p2). intros.
  invertClear H. invertClear H0. addHyp (Rle_or_lt x x0). invertClear H0.
  exists x. eapply mgSumL. assumption. apply H. assumption.
  exists x0. eapply mgSumR. apply H1. assumption. assumption. Qed.

(** If the body of a process definition is minGuard d, then so is the application.*)
Lemma mgAppEx : forall (x : list Var) (l : list Exp) (h : Name) (p : ProcTerm),
  def h = (x, p) -> (exists d, d %; (subProcTerm (listsToSub x l) p)) ->
  exists d, d %; (h $(l)$). intros. invertClear H0. exists x0. eapply mgApp.
  apply H. assumption. Qed.

(** More cumbersome version but it fills in the variable list x and the process p automatically by
extracting them from the process definition of p.*)
Lemma mgAppAutoEx : forall (l : list Exp) (h : Name),
  (exists d, d %; (subProcTerm (listsToSub (fst (def h)) l) (snd (def h)))) ->
  exists d, d %; (h $(l)$). intros. remember (def h) as e. destruct e.
  symmetry in Heqe. eapply mgAppEx. apply Heqe. assumption. Qed.

(** If the then branch of an ifThen construct is minGuard for some amount d,
then the whole construct is for some amount also.*)
Lemma mgThenBranchEx : forall (b : BoolExp) (p : ProcTerm),
  (exists d, d %; p) -> (exists d, d %; (b $> p)). intros.
  remember (evalBoolExpFunTot b). invertClear H. destruct b0.
  exists x. constructor. assumption. unfold evalBoolExpFunTot in Heqb0.
  apply evalBoolExpFunRel. destruct (evalBoolExpFun b); inversion Heqb0.
  reflexivity. exists (mkDelay onePos). apply mgIfFalse. symmetry.
  assumption. Qed.

(** If p has a minGuard, then so does the guarded term with p as the guarded process.*)
Lemma mgDelEx : forall (e : Exp) (p : ProcTerm),
  (exists d, d %; p) -> exists d, d %; ($<e>$p). intros.
  remember (evalExpFunTime e). destruct o.
  addHyp (Rle_lt_or_eq_dec 0 t (cond_nonneg t)). invertClear H0.
  exists (mkDelay (mkposreal t H1)). eapply mgDelEval. symmetry.
  apply Heqo. apply Rle_refl. invertClear H. exists x.
  apply mgDelTimeout. symmetry. symmetry in H1. apply timeZero in H1.
  rewrite <- H1. assumption. assumption. exists (mkDelay onePos).
  constructor. symmetry. assumption. Qed.
  

(**For every process there is some delay that is a minGuard of it.*)
Theorem minGuardExists (p : ProcTerm) :
  exists d, d %; p.
Proof.
  revert p. apply guarded_rect.
  - exists (mkDelay onePos). constructor.
  - apply mgOutEx.
  - apply mgInEx.
  - intros. apply mgThenBranchEx. assumption.
  - intros. apply mgSumEx; assumption.
  - intros p q [d1 H1] [d2 H2]. destruct (Rle_or_lt d1 d2).
    + exists d1. eapply mgParL; eassumption.
    + exists d2. eapply mgParR; eassumption.
  - intros h l H. apply mgAppAutoEx. rewrite <- unfoldApp_body. assumption.
  - intros. apply mgDelEx. assumption.
Qed.

(** For every application there is some delay that is a minGuard of that application.*)
Theorem minGuardExistsBody (h : Name) (l : list Exp) :
  exists d, d %; (h $(l)$).
Proof. apply minGuardExists. Qed.

(** An action that is involved in the sort relation is not the tau action.*)
Lemma sortNotTau (a : DiscAct) (p : ProcTerm) (d : Delay) :
  sort a d p -> a <> tauAct. unfold not. intros. apply sortInOrOut in H.
  invertClear H. invertClear H1. invertClear H; rewrite H1 in H0; inversion H0.
  Qed.

(** The precondition for parallel delay can be replaced with a simpler precondition
as long as the delay in question is a minGuard of both components of the parallel.*)
Theorem parPrecMgEquiv : forall (p q : ProcTerm) (d : Delay),
  d %; p -> d %; q -> (
  (forall a : DiscAct, sort a d p -> ~sort (a^) d q) <->
  (forall a : DiscAct, a <> tauAct -> discActEnabled p a -> ~discActEnabled q (a^))).
  intros; split; intros. unfold not; intros. addHyp (complementNotTau a H2).
  eapply enabledInSort in H3; [|assumption]. apply H1 in H3. apply H3. 
  eapply enabledInSort in H4; [|assumption]. apply H4.
  addHyp (sortNotTau a p d H2). apply sortMinGuard1 in H2; [|assumption].
  addHyp (H1 a H3 H2). clear H1. unfold not. intros. apply H4.
  eapply sortMinGuard1. apply H0. assumption. Qed.

Open Scope nat_scope.

(** A channel stamped with the types of the values that travel on it: for an output, the
types of the values it outputs, and for an input, the types of its variables. An output
and an input can synchronise exactly when their stamps agree.*)
Definition ChanStamped := (Channel * list ValType)%type.

(** We want a way to symbolically collect all the output actions a process can do.
For each output, we just record the channel on which it occurs and the types of the
values output, hence the collection is symbolic rather than literal.
Combined with a similar computation for input channels, this will be used to
construct a decision procedure as to whether processes can synchronise or not.*)
Inductive outListProc : ProcTerm -> list ChanStamped -> Prop :=
  | outlNil : outListProc nilProc []
  | outlOutEval (p : ProcTerm) (l : list Exp) (l' : list BaseType)
    (c : Channel) : evalExpLists l l' -> outListProc (c $< l >$ ! p) [(c, map valTypeOf l')]
  | outlOutIll (p : ProcTerm) (l : list Exp) (c : Channel) :
    (forall l', ~evalExpLists l l') -> outListProc (c $< l >$ ! p) []
  | outlIn (p : ProcTerm) (l : list Var) (c : Channel) :
    outListProc (c $< l >$ ? p) []
  | outlIfTrue (b : BoolExp) (p : ProcTerm) (l : list ChanStamped) :
    evalBoolExp b true -> outListProc p l -> outListProc (b $> p) l
  | outlIfFalse (b : BoolExp) (p : ProcTerm) :
    evalBoolExpFunTot b = false -> outListProc (b $> p) []
  | outlSum (p q : ProcTerm) (l1 l2 : list ChanStamped) :
    outListProc p l1 -> outListProc q l2 -> outListProc (p $+$ q) (l1 ++ l2)
  | outlPar (p q : ProcTerm) (l1 l2 : list ChanStamped) :
    outListProc p l1 -> outListProc q l2 -> outListProc (p $||$ q) (l1 ++ l2)
  | outlApp (h : Name) (l : list Exp) (l' : list ChanStamped) :
    outListProc (unfoldApp h l) l' -> outListProc (h $( l )$) l'
  | outlDelTimeout (p : ProcTerm) (e : Exp) (l : list ChanStamped) :
    evalExpFunTime e = Some zeroTime -> outListProc p l -> outListProc ($< e >$ p) l
  | outlDelGuard (p : ProcTerm) (e : Exp) :
    evalExpFunTime e <> Some zeroTime -> outListProc ($< e >$ p) [].

(** We want a way to symbolically collect all the input actions a process can do.
For each input, we just record the channel on which it occurs and the types of its
variables, hence the collection is symbolic rather than literal.
Combined with a similar computation for output channels, this will be used to
construct a decision procedure as to whether processes can synchronise or not.*)
Inductive inListProc : ProcTerm -> list ChanStamped -> Prop :=
  | inlNil : inListProc nilProc []
  | inlOut (p : ProcTerm) (l : list Exp) (c : Channel) :
    inListProc (c $< l >$ ! p) []
  | inlIn (p : ProcTerm) (l : list Var) (c : Channel) :
    inListProc (c $< l >$ ? p) [(c, map varType l)]
  | inlIfTrue (b : BoolExp) (p : ProcTerm) (l : list ChanStamped) :
    evalBoolExp b true -> inListProc p l -> inListProc (b $> p) l
  | inlIfFalse (b : BoolExp) (p : ProcTerm) :
    evalBoolExpFunTot b  = false -> inListProc (b $> p) []
  | inlSum (p q : ProcTerm) (l1 l2 : list ChanStamped) :
    inListProc p l1 -> inListProc q l2 -> inListProc (p $+$ q) (l1 ++ l2)
  | inlPar (p q : ProcTerm) (l1 l2 : list ChanStamped) :
    inListProc p l1 -> inListProc q l2 -> inListProc (p $||$ q) (l1 ++ l2)
  | inlApp (h : Name) (l : list Exp) (l' : list ChanStamped) :
    inListProc (unfoldApp h l) l' -> inListProc (h $( l )$) l'
  | inlDelTimeout (p : ProcTerm) (e : Exp) (l : list ChanStamped) :
    evalExpFunTime e = Some zeroTime -> inListProc p l -> inListProc ($< e >$ p) l
  | inlDelGuard (p : ProcTerm) (e : Exp) :
    evalExpFunTime e <> Some zeroTime -> inListProc ($< e >$ p) [].


(** If l and l' are both out lists of p, then l is equal to l'.*)
Theorem outListUnique (l l' : list ChanStamped) (p : ProcTerm) :
  outListProc p l -> outListProc p l' -> l = l'. intros.
  generalize dependent l'. induction H; intros;
  try solve [inversion H0; reflexivity].
  inversion H0. repeat f_equal. eapply evalExpListsUnique; eassumption.
  apply False_ind. eapply H5.
  apply H. inversion H0; [|reflexivity].
  apply False_ind. eapply H. apply H5. invertClear H1.
  eapply IHoutListProc. assumption. apply evalBoolExpTrueTot in H.
  rewrite H in H5. inversion H5. inversion H0.
  apply evalBoolExpTrueTot in H3. rewrite H3 in H. inversion H.
  reflexivity. invertClear H1. apply IHoutListProc1 in H4.
  apply IHoutListProc2 in H6. subst. reflexivity. 
  invertClear H1. apply IHoutListProc1 in H4. apply IHoutListProc2 in H6.
  subst. reflexivity. apply IHoutListProc. inversion H0. assumption.
  eapply IHoutListProc. inversion H1. assumption. apply False_ind.
  apply H5. assumption. inversion H0. apply False_ind.
  apply H. assumption. reflexivity. Qed.

(** If l and l' are both out lists of p, then l is equal to l'.*)
Theorem inListUnique (l l' : list ChanStamped) (p : ProcTerm) :
  inListProc p l -> inListProc p l' -> l = l'. intros.
  generalize dependent l'. induction H; intros;
  try solve [inversion H0; reflexivity].
  inversion H1. eapply IHinListProc. assumption.
  apply evalBoolExpTrueTot in H. rewrite H in H5. inversion H5.
  inversion H0; [|reflexivity].
  apply evalBoolExpTrueTot in H3. rewrite H3 in H. inversion H. 
  invertClear H1. apply IHinListProc1 in H4. apply IHinListProc2 in H6.
  subst. reflexivity. invertClear H1. apply IHinListProc1 in H4.
  apply IHinListProc2 in H6. subst. reflexivity.
  apply IHinListProc. inversion H0. assumption.
  eapply IHinListProc. inversion H1. assumption. apply False_ind.
  apply H5. assumption. inversion H0. apply False_ind.
  apply H. assumption. reflexivity. Qed.

(*Annoying workaround to make the following proof go through*)
Definition chanStampedNil : list ChanStamped := [].
(** All output prefixed terms have an associated output list.*)
Lemma outListInEx : forall (c : Channel) (l : list Var) (p : ProcTerm),
  {l' : list ChanStamped | outListProc (c $<l>$ ? p) l'}.
  intros. exists chanStampedNil. constructor. Qed.

(** All output prefixed terms have an associated output list.*)
Lemma outListOutEx : forall (c : Channel) (l : list Exp) (p : ProcTerm),
  { l' : list ChanStamped |outListProc (c $<l>$ ! p) l'}.
  intros. addHyp (evalExpListsExDec l).
  invertClear X. invertClear X0. exists [(c, map valTypeOf x)]. eapply outlOutEval.
  apply H. exists chanStampedNil. apply outlOutIll. unfold not. intros. apply H. exists l'.
  assumption. Qed.

(** If both components of a sum have some output list, then so does the whole sum.*)
Lemma outListSumEx : forall (p1 p2 : ProcTerm),
  {l1 | outListProc p1 l1} -> {l2 | outListProc p2 l2} ->
  {l | outListProc (p1 $+$ p2) l}. intros.
  invertClear H. invertClear H0. exists (x ++ x0). constructor; assumption.
  Qed.

(** If the body of a process definition has an output list, then so does the application.*)
Lemma outListAppIndEx : forall (x : list Var) (l : list Exp) (h : Name) (p : ProcTerm),
  def h = (x, p) -> {l' | outListProc (subProcTerm (listsToSub x l) p) l'} ->
  {l' | outListProc (h $(l)$) l'}. intros. invertClear H0. exists x0. constructor.
  unfold unfoldApp. rewrite H. apply H1. Qed.

(** More cumbersome version but it fills in the variable list x and the
process p automatically by extracting them from the process definition of p.*)
Lemma outListAppAutoEx : forall (l : list Exp) (h : Name),
  {l' | outListProc (subProcTerm (listsToSub (fst (def h)) l) (snd (def h))) l'} ->
  {l' | outListProc (h $(l)$) l'}. intros. remember (def h) as e. destruct e.
  symmetry in Heqe. eapply outListAppIndEx. apply Heqe. assumption. Qed.

(** If the then branch of an ifThen construct has some outListProc,
then the whole construct has one also.*)
Lemma outListThenBranchEx : forall (b : BoolExp) (p : ProcTerm),
  {l | outListProc p l} -> {l | outListProc (b $> p) l}. intros.
  remember (evalBoolExpFunTot b). invertClear H. destruct b0.
  exists x. constructor;[|assumption]. unfold evalBoolExpFunTot in Heqb0.
  apply evalBoolExpFunRel. destruct (evalBoolExpFun b); inversion Heqb0.
  reflexivity. exists chanStampedNil. apply outlIfFalse. symmetry.
  assumption. Qed.

(** If p has an output list, then so does the guarded term with p as
the guarded process.*)
Lemma outListDelEx : forall (e : Exp) (p : ProcTerm),
  {l | outListProc p l} -> {l | outListProc ($<e>$p) l}. intros.
  remember (evalExpFunTime e). destruct o.
  addHyp (eqDecTime t zeroTime). invertClear H0. invertClear H.
  exists x. constructor. symmetry. rewrite <- H1. assumption. assumption.
  exists chanStampedNil. apply outlDelGuard. unfold not. intro. apply H1.
  rewrite <- Heqo in H0. inversion H0.
  reflexivity. exists chanStampedNil. apply outlDelGuard. unfold not; intro.
  rewrite <- Heqo in H0. inversion H0. Qed.


(**For every process there is a list of output actions for that process.*)
Theorem outListEx (p : ProcTerm) : {l : list ChanStamped | outListProc p l}.
Proof.
  revert p. apply guarded_rect.
  - exists chanStampedNil. constructor.
  - apply outListOutEx.
  - apply outListInEx.
  - intros. apply outListThenBranchEx. assumption.
  - intros. apply outListSumEx; assumption.
  - intros p q [l1 H1] [l2 H2]. exists (l1 ++ l2). constructor; assumption.
  - intros h l [l' H]. exists l'. constructor. assumption.
  - intros. apply outListDelEx. assumption.
Qed.

(**Every application term has a list of output actions.*)
Theorem outListAppEx (h : Name) (l : list Exp) :
  {l' : list ChanStamped | outListProc (h $(l)$) l'}.
Proof. apply outListEx. Qed.

(** All input prefixed terms have an associated input list.*)
Lemma inListInEx : forall (c : Channel) (l : list Var) (p : ProcTerm),
  {l' : list ChanStamped | inListProc (c $<l>$ ? p) l'}.
  intros. exists [(c, map varType l)]. constructor. Qed.

(** All input prefixed terms have an associated input list.*)
Lemma inListOutEx : forall (c : Channel) (l : list Exp) (p : ProcTerm),
  { l' : list ChanStamped |inListProc (c $<l>$ ! p) l'}.
  intros. exists chanStampedNil. constructor. Qed.

(** If both components of a sum have some input list, then so does the whole sum.*)
Lemma inListSumEx : forall (p1 p2 : ProcTerm),
  {l1 | inListProc p1 l1} -> {l2 | inListProc p2 l2} ->
  {l | inListProc (p1 $+$ p2) l}. intros.
  invertClear H. invertClear H0. exists (x ++ x0). constructor; assumption.
  Qed.

(** If the body of a process definition has an input list, then so does the application.*)
Lemma inListAppIndEx : forall (x : list Var) (l : list Exp) (h : Name) (p : ProcTerm),
  def h = (x, p) -> {l' | inListProc (subProcTerm (listsToSub x l) p) l'} ->
  {l' | inListProc (h $(l)$) l'}. intros. invertClear H0. exists x0. constructor.
  unfold unfoldApp. rewrite H. apply H1. Qed.

(** More cumbersome version but it fills in the variable list x and the
process p automatically by extracting them from the process definition of p.*)
Lemma inListAppAutoEx : forall (l : list Exp) (h : Name),
  {l' | inListProc (subProcTerm (listsToSub (fst (def h)) l) (snd (def h))) l'} ->
  {l' | inListProc (h $(l)$) l'}. intros. remember (def h) as e. destruct e.
  symmetry in Heqe. eapply inListAppIndEx. apply Heqe. assumption. Qed.

(** If the then branch of an ifThen construct has some inListProc,
then the whole construct has one also.*)
Lemma inListThenBranchEx : forall (b : BoolExp) (p : ProcTerm),
  {l | inListProc p l} -> {l | inListProc (b $> p) l}. intros.
  remember (evalBoolExpFunTot b). invertClear H. destruct b0.
  exists x. constructor;[|assumption]. unfold evalBoolExpFunTot in Heqb0.
  apply evalBoolExpFunRel. destruct (evalBoolExpFun b); inversion Heqb0.
  reflexivity. exists chanStampedNil. apply inlIfFalse. symmetry.
  assumption. Qed.

(** If p has an input list, then so does the guarded term with p as
the guarded process.*)
Lemma inListDelEx : forall (e : Exp) (p : ProcTerm),
  {l | inListProc p l} -> {l | inListProc ($<e>$p) l}. intros.
  remember (evalExpFunTime e). destruct o.
  addHyp (eqDecTime t zeroTime). invertClear H0. invertClear H.
  exists x. constructor. symmetry. rewrite <- H1. assumption. assumption.
  exists chanStampedNil. apply inlDelGuard. unfold not. intro. apply H1.
  rewrite <- Heqo in H0. inversion H0.
  reflexivity. exists chanStampedNil. apply inlDelGuard. unfold not; intro.
  rewrite <- Heqo in H0. inversion H0. Qed.


(**For every process there is a list of input actions for that process.*)
Theorem inListEx (p : ProcTerm) : {l : list ChanStamped | inListProc p l}.
Proof.
  revert p. apply guarded_rect.
  - exists chanStampedNil. constructor.
  - apply inListOutEx.
  - apply inListInEx.
  - intros. apply inListThenBranchEx. assumption.
  - intros. apply inListSumEx; assumption.
  - intros p q [l1 H1] [l2 H2]. exists (l1 ++ l2). constructor; assumption.
  - intros h l [l' H]. exists l'. constructor. assumption.
  - intros. apply inListDelEx. assumption.
Qed.

(**Every application term has a list of input actions.*)
Theorem inListAppEx (h : Name) (l : list Exp) :
  {l' : list ChanStamped | inListProc (h $(l)$) l'}.
Proof. apply inListEx. Qed.

(**Equality is decidable on stamped channels.*)
Lemma eqDecChanStamped (c1 c2 : ChanStamped) :
  {c1 = c2} + {c1 <> c2}. destruct c1 as [c l], c2 as [c0 l0].
  destruct (eqDecChannel c c0) as [E | NE];
    [subst | right; intro H; apply NE; inversion H; reflexivity].
  destruct (list_eq_dec valTypeEqDec l l0) as [E | NE];
    [subst; left; reflexivity | right; intro H; apply NE; inversion H; reflexivity].
  Qed.

(** It is decidable whether or not an element is in a list of stamped channels.*)
Lemma inChanStampedDec (s : ChanStamped) (l : list ChanStamped) : 
  {s _: l} + {~s _: l}. apply in_dec. apply eqDecChanStamped. Qed.











































(** If a stamped channel is in the output list of a process, then that process is
enabled on an action that matches the stamped channel.*)
Theorem outListEnabled (c : Channel) (p : ProcTerm) (l : list ChanStamped)
  (tys : list ValType) : outListProc p l -> (c, tys) _: l ->
  exists v, map valTypeOf v = tys /\ discActEnabled p (c ;! v). intros.
  induction H; try solve [inversion H0]. exists l'. 
  invertClear H0. invertClear H1. split. reflexivity.
  eapply dae. apply stepDpOut. assumption.
  inversion H1. apply IHoutListProc in H0. invertClear H0.
  exists x. invertClear H2. split. assumption. clear H0. rename H3 into H2.
  apply daeThenBranch; assumption. apply in_app_or in H0.
  invertClear H0. apply IHoutListProc1 in H2. invertClear H2.
  exists x. invertClear H0. split. assumption. clear H2. rename H3 into H0.
  apply daeSumL. assumption. apply IHoutListProc2 in H2.
  invertClear H2. exists x.
  invertClear H0. split. assumption. clear H2. rename H3 into H0.
  apply daeSumR. assumption.
  apply in_app_or in H0. invertClear H0. apply IHoutListProc1 in H2.
  invertClear H2. exists x.
  invertClear H0. split. assumption. clear H2. rename H3 into H0.
  apply daeParL. assumption. apply IHoutListProc2 in H2.
  invertClear H2. exists x.
  invertClear H0. split. assumption. clear H2. rename H3 into H0.
  apply daeParR. assumption.
  apply IHoutListProc in H0. invertClear H0. exists x.
  remember (def h). destruct p as [lx p].
  invertClear H1. split. assumption. clear H0. rename H2 into H1.
  eapply daeApp.
  symmetry. apply Heqp. unfold unfoldApp in H1. rewrite <- Heqp in H1.
  assumption. apply IHoutListProc in H0. invertClear H0. exists x.
  invertClear H2. split. assumption. clear H0. rename H3 into H2.
  invertClear H2. eapply dae. constructor. apply H0.
  assumption. Qed.

Theorem inListEnabled (c : Channel) (p : ProcTerm) (l : list ChanStamped)
  (v : list BaseType): inListProc p l -> (c, map valTypeOf v) _: l ->
  discActEnabled p (c ;? v). intros.
  induction H; try solve [inversion H0]. eapply dae.
  invertClear H0. invertClear H. apply stepDpIn. apply typedVals_map. congruence.
  inversion H. apply IHinListProc in H0.
  apply daeThenBranch; assumption. apply in_app_or in H0.
  invertClear H0. apply IHinListProc1 in H2.
  apply daeSumL; assumption. apply IHinListProc2 in H2.
  apply daeSumR. assumption.
  apply in_app_or in H0. invertClear H0. apply IHinListProc1 in H2.
  apply daeParL; assumption. apply IHinListProc2 in H2.
  apply daeParR; assumption.
  apply IHinListProc in H0. remember (def h). destruct p as [lx p].
  eapply daeApp. symmetry. apply Heqp. unfold unfoldApp in H0.
  rewrite <- Heqp in H0. assumption. apply IHinListProc in H0. invertClear H0.
  eapply dae. constructor. apply H2.
  assumption. Qed.



(** If a process is enabled on an output action then there is a matching stamped
channel in the output list of that process.*)
Theorem enabledOutList (c : Channel) (p : ProcTerm) (l : list ChanStamped)
  (v : list BaseType) :  outListProc p l -> discActEnabled p (c ;! v) ->
  (c, map valTypeOf v) _: l. intros. invertClear H0. generalize dependent p'.
  induction H; intros; try solve [inversion H1]. inversion H1.
  rewrite (evalExpListsUnique _ _ _ H H7). constructor.
  reflexivity. inversion H1. apply False_ind. eapply H.
  apply H7. invertClear H1. apply IHoutListProc in H4. assumption.
  inversion H1. rewrite H in H6. inversion H6. inversion H1.
  apply IHoutListProc1 in H6. apply in_or_app. left. assumption.
  apply IHoutListProc2 in H6. apply in_or_app. right. assumption.
  inversion H1. apply IHoutListProc1 in H6. apply in_or_app. left. assumption.
  apply IHoutListProc2 in H6. apply in_or_app. right. assumption. 
  inversion H1. unfold unfoldApp in IHoutListProc. rewrite H3 in IHoutListProc.
  eapply IHoutListProc. apply H6. invertClear H1. apply IHoutListProc in H4.
  assumption. inversion H1. false. Qed.

(** If a process is enabled on an input action then there is a matching stamped
channel in the input list of that process.*)
Theorem enabledInList (c : Channel) (p : ProcTerm) (l : list ChanStamped)
  (v : list BaseType) : inListProc p l -> discActEnabled p (c ;? v) ->
  (c, map valTypeOf v) _: l. intros. invertClear H0. generalize dependent p'.
  induction H; intros; try solve [inversion H1]. inversion H1.
  apply typedVals_map in H6. rewrite H6. constructor. reflexivity.
  inversion H1. apply IHinListProc in H4. assumption.
  inversion H1. rewrite H6 in H. inversion H. inversion H1.
  apply IHinListProc1 in H6. apply in_or_app. left. assumption.
  apply IHinListProc2 in H6. apply in_or_app. right. assumption.
  inversion H1. apply IHinListProc1 in H6. apply in_or_app. left. assumption.
  apply IHinListProc2 in H6. apply in_or_app. right. assumption. 
  inversion H1. unfold unfoldApp in IHinListProc. rewrite H3 in IHinListProc.
  eapply IHinListProc. apply H6. invertClear H1. apply IHinListProc in H4.
  assumption. inversion H1. false. Qed.

(** A way of checking for no synchronisations between p and q by performing intersections
on their input/output and output/input lists and checking that they evaluate to empty lists.*)
Inductive noSync (p q : ProcTerm) : Prop :=
  nosync : forall (l1 l2 l1' l2' : list ChanStamped),
  inListProc p l1 -> outListProc p l2 -> inListProc q l1' -> outListProc q l2' ->
  set_inter eqDecChanStamped l1 l2' = [] -> set_inter eqDecChanStamped l2 l1' = []
  -> noSync p q.

(**The no sync predicate is decidable.*)
Theorem noSyncDec (p q : ProcTerm) :
  decidable (noSync p q). addHyp (inListEx p). addHyp (inListEx q).
  addHyp (outListEx p). addHyp (outListEx q). invertClear H.
  invertClear H0. invertClear H1. invertClear H2.
  rename x into l1, x0 into l3, x1 into l2, x2 into l4.
  remember (set_inter eqDecChanStamped l1 l4).
  remember (set_inter eqDecChanStamped l2 l3).
  destruct s. destruct s0. left. eapply nosync. apply H3.
  apply H0. apply H. apply H1. symmetry. assumption.
  symmetry. assumption. right. unfold not. intro.
  inversion H2. replace l5 with l2 in H9.
  replace l1' with l3 in H9. rewrite H9 in Heqs0.
  inversion Heqs0. eapply inListUnique. apply H. assumption.
  eapply outListUnique. apply H0. assumption.
  right. unfold not. intro.
  inversion H2. replace l0 with l1 in H8.
  replace l2' with l4 in H8. rewrite H8 in Heqs.
  inversion Heqs. eapply outListUnique. apply H1. assumption.
  eapply inListUnique. apply H3. assumption. Qed.

(** The precondition for parallel delay can be replaced with a simpler precondition
involving the input and output lists, as long as the delay in question is a minGuard
of both components of the parallel.*)
Theorem parPrecMgEquiv2 : forall (p q : ProcTerm) (d : Delay),
  d %; p -> d %; q -> (
  (forall a : DiscAct, sort a d p -> ~sort (a^) d q) <->
  noSync p q). intros. rewrite parPrecMgEquiv; [|assumption|assumption].
  (**Left to right.*)
  split. addHyp (inListEx p). addHyp (inListEx q).
  addHyp (outListEx p). addHyp (outListEx q). invertClear H1.
  invertClear H2. invertClear H3. invertClear H4.
  rename x into l1, x0 into l3, x1 into l2, x2 into l4.
  remember (set_inter eqDecChanStamped l1 l4).
  remember (set_inter eqDecChanStamped l2 l3). intros.
  destruct s. destruct s0.
  eapply nosync. apply H5. apply H2. apply H1. apply H3.
  rewrite Heqs. reflexivity. symmetry. assumption.
  (*Contradiction out p, in q.*)
  assert (set_In c (set_inter eqDecChanStamped l2 l3)).
  rewrite <- Heqs0. constructor. reflexivity.
  addHyp H6. (apply set_inter_elim1 in H6). (apply set_inter_elim2 in H7).
  unfold set_In in H6, H7. destruct c as [c n].
  addHyp (outListEnabled c p l2 n H2 H6). invertClear H8. invertClear H9.
  rewrite <- H8 in H7. addHyp (inListEnabled c q l3 x H1 H7).
  apply False_ind. apply H4 with (a := (c;! x)); try assumption.
  unfold not. intros. inversion H11.
  (*Contradiction out q, in p.*) 
  assert (set_In c (set_inter eqDecChanStamped l1 l4)).
  rewrite <- Heqs. constructor. reflexivity.
  addHyp H6. (apply set_inter_elim1 in H6). (apply set_inter_elim2 in H7).
  unfold set_In in H6, H7. destruct c as [c n].
  addHyp (outListEnabled c q l4 n H3 H7). invertClear H8. invertClear H9.
  rewrite <- H8 in H6. addHyp (inListEnabled c p l1 x H5 H6).
  apply False_ind. apply H4 with (a := (c;? x)); try assumption.
  unfold not. intros. inversion H11.
  (**Right to left.*)
  unfold not. intros. invertClear H1.
  destruct a; [clear H2 | clear H2 | apply H2; reflexivity].
  rename l into v. addHyp (enabledInList c p l1 v H5 H3).
  simpl in H4. addHyp (enabledOutList c q l2' v H8 H4).
  addHyp (set_inter_intro eqDecChanStamped (c, map valTypeOf v) l1 l2' H1 H2).
  rewrite H9 in H11. inversion H11.
  rename l into v. addHyp (enabledOutList c p l2 v H6 H3).
  simpl in H4. addHyp (enabledInList c q l1' v H7 H4).
  addHyp (set_inter_intro eqDecChanStamped (c, map valTypeOf v) l2 l1' H1 H2).
  rewrite H10 in H11. inversion H11. Qed.

(**For any pair of processes, there is a minGuard that is common to both.*)
Lemma minGuardCommon (p q : ProcTerm) : exists d,
  d %; p /\ d %; q. addHyp (minGuardExists p). addHyp (minGuardExists q).
  invertClear H. invertClear H0. addHyp (Rle_lt_dec x x0).
  invertClear H0. exists x. split. assumption. eapply minGuardLe.
  apply H. assumption. exists x0. apply Rlt_le in H2. split.
  eapply minGuardLe. apply H1; assumption. assumption. assumption. Qed.

(**For any pair of delay enabled processes, there is a delay that is common to both.*)
Lemma taeCommon (p1 p2 : ProcTerm) :
  (exists d, timedActEnabled p1 d) -> (exists d, timedActEnabled p2 d) ->
  (exists d, timedActEnabled p1 d /\ timedActEnabled p2 d).
  intros. invertClear H. invertClear H0. addHyp (Rle_lt_dec x x0).
  invertClear H0. exists x. split. assumption. eapply delShorten.
  apply H. assumption. exists x0. apply Rlt_le in H2. split.
  eapply delShorten. apply H1; assumption. assumption. assumption. Qed.
   

(** If a process p is time act enabled on d, then it is time act enabled on
any minGuard d' of p less than d.*)
Lemma taeMinGuardCommon (p1 p2 : ProcTerm) :
  (exists d, timedActEnabled p1 d) -> (exists d, timedActEnabled p2 d) ->
  (exists d, timedActEnabled p1 d /\ timedActEnabled p2 d /\ d %; p1 /\ d %; p2).
  intros. addHyp (taeCommon p1 p2 H H0). clear H. clear H0. invertClear H1.
  invertClear H. addHyp (minGuardCommon p1 p2). invertClear H.
  addHyp (Rle_lt_dec x x0). invertClear H2. invertClear H. exists x.
  apply minGuardLe with (d1 := x) in H3.
  apply minGuardLe with (d1 := x) in H4.
  repeat (split; [assumption|]). assumption. assumption. assumption.
  apply Rlt_le in H2. exists x0.
  apply delShorten with (d' := x0) in H0. apply delShorten with (d' := x0) in H1.
  repeat (split; [assumption|]). assumption. assumption. assumption. Qed.

(** If the noSync predicate is not true, then there exists some specific synchronisation
between the component processes.*)
Lemma noSyncNotExistsSync (p q : ProcTerm) : ~noSync p q ->
  exists a, discActEnabled p a /\ discActEnabled q (a^).
  intros. addHyp (inListEx p). addHyp (inListEx q).
  addHyp (outListEx p). addHyp (outListEx q). invertClear H1.
  invertClear H2. invertClear H3. invertClear H0.
  rename x into l1, x0 into l3, x1 into l2, x2 into l4.
  remember (set_inter eqDecChanStamped l4 l2).
  remember (set_inter eqDecChanStamped l3 l1).
  destruct s. destruct s0.
  (** If both list are empty, then we get a contradiction.*)
  apply False_ind. apply H. eapply nosync. apply H3. apply H1.
  apply H4. apply H2. symmetry. assumption. symmetry. assumption.
  (** Otherwise we just take the head of the list as a witness.*)
  assert (set_In c (set_inter eqDecChanStamped l3 l1)).
  rewrite <- Heqs0. constructor. reflexivity.
  addHyp H0. (apply set_inter_elim1 in H0). (apply set_inter_elim2 in H5).
  unfold set_In in H0, H5. destruct c as [c n].
  addHyp (outListEnabled c p l3 n H1 H0). invertClear H6. invertClear H7.
  rewrite <- H6 in H5. addHyp (inListEnabled c q l1 x H4 H5).
  exists (c ;! x). split; assumption.
  (**And do the very same for the symmetrical case.*)
  assert (set_In c (set_inter eqDecChanStamped l4 l2)).
  rewrite <- Heqs. constructor. reflexivity.
  addHyp H0. (apply set_inter_elim1 in H0). (apply set_inter_elim2 in H5).
  unfold set_In in H0, H5. destruct c as [c n].
  addHyp (outListEnabled c q l2 n H2 H5). invertClear H6. invertClear H7.
  rewrite <- H6 in H0. addHyp (inListEnabled c p l4 x H3 H0).
  exists (c ;? x). split; assumption. Qed.

(**Progress says that a process can either delay or perform a tau.*)
Definition progress (p : ProcTerm) : Prop :=
   discActEnabled p tauAct \/ exists d, timedActEnabled p d.

(** All input prefixed terms can progress.*)
Lemma progressIn : forall (c : Channel) (l : list Var) (p : ProcTerm),
  progress (c $<l>$ ? p). unfold progress.
  intros. right. exists (mkDelay onePos). eapply tae. constructor. Qed.

(** All output prefixed terms can progress.*)
Lemma progressOut : forall (c : Channel) (l : list Exp) (p : ProcTerm),
  progress (c $<l>$ ! p). unfold progress.
  intros. right. exists (mkDelay onePos). eapply tae. constructor. Qed.

(** If both components of a sum can progress, then so can the whole sum.*)
Lemma progressSum : forall (p1 p2 : ProcTerm),
  progress p1 -> progress p2 -> progress (p1 $+$ p2). unfold progress. intros.
  invertClear H. left. apply daeSumL. assumption. invertClear H0. left.
  apply daeSumR. assumption. right. apply taeSumEx; assumption. Qed.

(** If the body of a process definition can progress, then so can the application.*)
Lemma progressAppInd : forall (x : list Var) (l : list Exp) (h : Name) (p : ProcTerm),
  def h = (x, p) -> progress (subProcTerm (listsToSub x l) p) ->
  progress (h $(l)$). unfold progress. intros. invertClear H0; [left|right].
  eapply daeApp. apply H. assumption. inversion H1. exists x0. eapply taeApp.
  apply H. assumption. Qed.

(** More cumbersome version but it fills in the variable list x and the
process p automatically by extracting them from the process definition of p.*)
Lemma progressAppAuto : forall (l : list Exp) (h : Name),
  progress (subProcTerm (listsToSub (fst (def h)) l) (snd (def h))) ->
  progress (h $(l)$). intros. remember (def h) as e. destruct e.
  symmetry in Heqe. eapply progressAppInd. apply Heqe. assumption. Qed.

(** If the then branch of an ifThen construct can progress,
then the whole construct can also.*)
Lemma progressThenBranch : forall (b : BoolExp) (p : ProcTerm),
  progress p -> progress (b $> p). intros.
  remember (evalBoolExpFunTot b). destruct b0. invertClear H.
  left. apply daeThenBranch. rewrite evalBoolExpTrueTot.
  symmetry. assumption. assumption. right. invertClear H0.
  exists x. apply taeThenBranch. assumption.
  right. exists (mkDelay onePos).
  eapply tae. apply stepTpIfFalse. symmetry. assumption. Qed.

Open Scope R_scope.

(** If p can progress, then so can the guarded term with p as
the guarded process.*)
Lemma progressDel : forall (e : Exp) (p : ProcTerm),
  progress p -> progress ($<e>$p). intros.
  remember (evalExpFunTime e). destruct o.
  addHyp (eqDecTime t zeroTime). invertClear H0.
  symmetry in Heqo. rewrite H1 in Heqo.
  invertClear H;[left|right].
  invertClear H0. eapply dae. constructor. apply H. assumption.
  invertClear H0. exists x. apply taeDel. apply H.
  right. assert (0 < t). addHyp (cond_nonneg t). apply Rle_lt_or_eq_dec in H0.
  invertClear H0. assumption. apply False_ind. apply H1.
  apply timeZero. symmetry. assumption. remember (mkDelay (mkposreal t H0)).
  assert (d <= t). rewrite Heqd. apply Rle_refl. exists d.
  eapply tae. apply stepTpDelSub with (H := H2).
  symmetry. apply Heqo. right. exists (mkDelay onePos). eapply tae. eapply stepTpDelIll.
  symmetry. assumption. Qed.

(** A software process can always do either a tau action or it can delay by some amount
d.*)
Theorem progressSoft : forall (p : ProcTerm),
  progress p.
Proof.
  apply guarded_rect.
  - right. exists (mkDelay onePos). eapply tae. constructor.
  - apply progressOut.
  - apply progressIn.
  - apply progressThenBranch.
  - apply progressSum.
  (*Case: par*)
  - intros p1 p2 IHp1 IHp2. unfold progress in *.
  invertClear IHp1. left. invertClear H. eapply dae. constructor. apply H0.
  invertClear IHp2. left. invertClear H0. eapply dae. apply stepDpParR. apply H1.
  (**Special case: par- both can delay. We now do case analysis on whether or not
  p and q can synchronise.*)
  addHyp (noSyncDec p1 p2). invertClear H1; [right | left].
  addHyp (taeMinGuardCommon p1 p2 H H0). invertClear H1.
  decompose [and] H3. clear H3. rename x into d. exists d.
  invertClear H1. invertClear H5. eapply tae. constructor. apply H3.
  apply H1. rewrite parPrecMgEquiv2; assumption.
  (**Now we're at the case where they don't synchronise.*)
  apply noSyncNotExistsSync in H2. invertClear H2. invertClear H1.
  invertClear H2. invertClear H3. destruct x; eapply dae.
  eapply stepDpSyncRL. apply H1. apply H2.
  eapply stepDpSyncLR. apply H1. apply H2.
  eapply stepDpParL. apply H1.
  (*Case: app*)
  - intros h l H. apply progressAppAuto. rewrite <- unfoldApp_body. assumption.
  (*Case: del*)
  - apply progressDel.
Qed.

(**Every application term can progress.*)
Theorem progressApp (h : Name) (l : list Exp) :
  progress (h $(l)$).
Proof. apply progressSoft. Qed.

(** If a process cannot perform a tau action, then it can delay by some amount. This is
a direct corollary of progress.*)
Corollary patienceSoft (p : ProcTerm) : ~discActEnabled p tauAct -> exists d,
  timedActEnabled p d. intros. addHyp (progressSoft p). invertClear H0.
  apply False_ind. apply H. assumption. assumption. Qed.

(** A delay of d' from a guard with d already taken off it is a delay of d + d' from the
original guard. The guard must evaluate to t: an ill-formed guard idles instead.*)
Lemma delProc_minus_guard t d d' H p p' e :
  evalExpFunTime e = Some t ->
  $< minusTime t (delay d) H >$ p -PD- d' -PD> p' ->
  $< e >$ p -PD- d +d+ d' -PD> p'.
Proof using PNames PDefs.
  intros E S. inversion S; subst; clear S;
    match goal with [E2 : evalExpFunTime (eBase (baseTime _)) = _ |- _] =>
      rewrite evalExpFunTime_time in E2; try (inversion E2; subst; clear E2) end.
  - (* the remaining guard runs out within d' *)
    replace (d +d+ (minusTime t (delay d) H +dt+ d0)) with (t +dt+ d0).
    + apply stepTpDelAdd; assumption.
    + apply delayEqR. simpl. ring.
  - (* d' is within the remaining guard *)
    match goal with [H0 : pos (delay d') <= _ |- _] =>
    assert (H' : pos (delay (d +d+ d')) <= nonneg (time t))
      by (simpl in H0 |- *;
          replace (nonneg (time t)) with (pos (delay d) + (nonneg (time t) - pos (delay d)))
            by ring;
          apply Rplus_le_compat_l; exact H0);
    replace ($< minusTime (minusTime t (delay d) H) (delay d') H0 >$ p)
      with ($< minusTime t (delay (d +d+ d')) H' >$ p) end.
    + apply stepTpDelSub; assumption.
    + do 3 f_equal. apply timeEqR. simpl. ring.
Qed.

(** If p can delay to p' and p' can delay to p'',
 then p can delay to p'' by the sum of the two original delays.*)
Theorem delAddSoft (p p' p'' : ProcTerm) (d d' : Delay) :
  p -PD- d -PD> p' -> p' -PD- d' -PD> p'' -> p -PD- d +d+ d' -PD> p''.
  intro. generalize dependent p''. induction H; intros;
  try solve [inversion H; constructor].
  constructor. apply IHstepTimedProc. assumption. assumption.
  inversion H0. rewrite H in H6. inversion H6. apply stepTpIfFalse. assumption.
  (*Sum*)
  inversion H1. constructor. apply IHstepTimedProc1; assumption.
  apply IHstepTimedProc2; assumption.
  (*Parallel*)
  inversion H2. constructor. apply IHstepTimedProc1; assumption.
  apply IHstepTimedProc2; assumption.
  intro. repeat rewrite <- sortDerivEquiv. apply H9. assumption.
  assumption.
  (*Name*)
  eapply stepTpApp. apply H. apply IHstepTimedProc. assumption.
  (*The del cases*)
  rewrite delTimeAddAssoc2. eapply stepTpDelAdd. apply IHstepTimedProc.
  assumption. assumption. eapply delProc_minus_guard; eassumption.  
  inversion H0; [rewrite H in H6; inversion H6 .. | ]. 
  apply stepTpDelIll. assumption. Qed.  

(** The passage of time in this universe is linear, i.e. any process can delay by an amount d to
at most one derivative process.*)
Theorem timeDeterminacySoft (p p1' p2' : ProcTerm) (d : Delay) :
  p -PD- d -PD> p1' -> p -PD- d -PD> p2' -> p1' = p2'.
  intros. generalize dependent p2'.
  induction H; intros; try solve [inversion H0; reflexivity].
  inversion H1. apply IHstepTimedProc; assumption.
  rewrite H0 in H6. inversion H6. inversion H0.
  rewrite H in H6. inversion H6. reflexivity.
  inversion H1. f_equal. apply IHstepTimedProc1; assumption.
  apply IHstepTimedProc2; assumption.
  inversion H2. f_equal. apply IHstepTimedProc1; assumption.
  apply IHstepTimedProc2; assumption.
  inversion H1. apply IHstepTimedProc. rewrite H in H4.
  inversion H4. assumption.
  (*Now the del cases*)
  (*DEL1*)
  inversion H1. replace t0 with t in H4. apply Rplus_eq_reg_l in H4.
  apply delayEqR in H4. rewrite H4 in H5.
  apply IHstepTimedProc; assumption. cut (baseTime t = baseTime t0).
  intros. inversion H8. reflexivity.
  rewrite H0 in H7. inversion H7. reflexivity.
  assert (t = t0). cut (baseTime t = baseTime t0).
  intros. inversion H8. reflexivity.
  rewrite H0 in H7. inversion H7. reflexivity.  
  apply False_ind. clear H6. rewrite H8 in H2.
  eapply Rlt_not_le; [|apply H2]. simpl. Rplus_lt_tac. delPos.
  rewrite H0 in H6. inversion H6.
  (*DEL2*)
  inversion H1. assert (t = t0). rewrite H0 in H7. inversion H7.
  reflexivity. false. rewrite H8 in H. rewrite <- H5 in H.
  simpl in H. apply Rplus_le_swap_ll in H. apply Rle_not_lt in H.
  apply H. Rminus_refl_simpl. delPos.
  assert (t = t0). rewrite H0 in H7. inversion H7.
  reflexivity. subst. repeat f_equal. apply proof_irrelevance.
  rewrite H0 in H6. inversion H6.
  (*DEL3*)
  inversion H0; [rewrite H in H6; inversion H6.. | ].
  reflexivity. Qed.



(*********Delays to self and inversion of parallel steps*********)

(** The nil process delays only to itself.*)
Lemma del_self_nil : forall d q, nilProc -PD- d -PD> q -> q = nilProc.
Proof. intros d q H. inversion H. reflexivity. Qed.

(** An output prefix delays only to itself.*)
Lemma del_self_outPrefix c l p : forall d q, c $< l >$ ! p -PD- d -PD> q -> q = c $< l >$ ! p.
Proof. intros d q H. inversion H. reflexivity. Qed.

(** An input prefix delays only to itself.*)
Lemma del_self_inPrefix c xs p : forall d q, c $< xs >$ ? p -PD- d -PD> q -> q = c $< xs >$ ? p.
Proof. intros d q H. inversion H. reflexivity. Qed.

(** A sum of processes that delay only to themselves delays only to itself.*)
Lemma del_self_sum p1 p2 :
  (forall d q, p1 -PD- d -PD> q -> q = p1) -> (forall d q, p2 -PD- d -PD> q -> q = p2) ->
  forall d q, p1 $+$ p2 -PD- d -PD> q -> q = p1 $+$ p2.
Proof.
  intros H1 H2 d q H. inversion H; subst.
  f_equal; [eapply H1 | eapply H2]; eassumption.
Qed.

(** A discrete step of a parallel pair is a step of one component, or the two
synchronising on complementary actions.*)
Lemma par_disc_inv p q a r : p $||$ q -PA- a -PA> r -> exists p' q', r = p' $||$ q' /\
  ((p -PA- a -PA> p' /\ q = q') \/ (q -PA- a -PA> q' /\ p = p') \/
   (a = tauAct /\ exists c v,
     (p -PA- c ;! v -PA> p' /\ q -PA- c ;? v -PA> q') \/
     (p -PA- c ;? v -PA> p' /\ q -PA- c ;! v -PA> q'))).
Proof.
  intro H. inversion H; subst; do 2 eexists; (split; [reflexivity | ]).
  - left. split; [eassumption | reflexivity].
  - right. left. split; [eassumption | reflexivity].
  - right. right. split; [reflexivity | ]. do 2 eexists. left. split; eassumption.
  - right. right. split; [reflexivity | ]. do 2 eexists. right. split; eassumption.
Qed.

(** A parallel pair delays by both components delaying.*)
Lemma par_del_inv p q d r : p $||$ q -PD- d -PD> r ->
  exists p' q', r = p' $||$ q' /\ p -PD- d -PD> p' /\ q -PD- d -PD> q'.
Proof.
  intro H. inversion H; subst. do 2 eexists.
  split; [reflexivity | split; eassumption].
Qed.

(*********N-ary parallel composition*********)
(** The results below are about parAll p ps, the composition of any number of components.
A step at a position of the list of components is a stepAt, and a fact about every
component is a Forall2.*)

(** A component's discrete step is a step of the whole, the other components unchanged.*)
Lemma parAll_disc_intro a i p ps p' ps' :
  stepAt (fun q q' => q -PA- a -PA> q') i (p :: ps) (p' :: ps') ->
  parAll p ps -PA- a -PA> parAll p' ps'.
Proof.
  revert i p p' ps'. induction ps as [ |q qs IH]; intros i p p' ps' St;
    inversion St; subst; simpl.
  - assumption.
  - match goal with [K : stepAt _ _ [] _ |- _] => inversion K end.
  - constructor. assumption.
  - destruct ps' as [ |q' qs'];
      [match goal with [K : stepAt _ _ (_ :: _) [] |- _] => inversion K end | ].
    apply stepDpParR. eapply IH. eassumption.
Qed.

(** A component's enabledness lifts to the whole.*)
Lemma parAll_dae_intro p ps q a :
  In q (p :: ps) -> discActEnabled q a -> discActEnabled (parAll p ps) a.
Proof.
  revert p. induction ps as [ |q0 qs IH]; intros p [E | I] D; simpl; subst.
  - assumption.
  - inversion I.
  - apply daeParL. assumption.
  - apply daeParR. apply IH; assumption.
Qed.

(** A component's sort lifts to the whole.*)
Lemma parAll_sort_intro p ps q a d :
  In q (p :: ps) -> sort a d q -> sort a d (parAll p ps).
Proof.
  revert p. induction ps as [ |q0 qs IH]; intros p [E | I] S; simpl; subst.
  - assumption.
  - inversion I.
  - apply sortParCompL. assumption.
  - apply sortParCompR. apply IH; assumption.
Qed.

(** A discrete step of a parallel composition is a step of one component, or an output of
one component synchronising with an input of another; the other components are unchanged.*)
Lemma parAll_disc_inv p ps a r : parAll p ps -PA- a -PA> r ->
  exists p' ps', r = parAll p' ps' /\
  ((exists i, stepAt (fun q q' => q -PA- a -PA> q') i (p :: ps) (p' :: ps')) \/
   (a = tauAct /\ exists i j c v l, i <> j /\
     stepAt (fun q q' => q -PA- c ;! v -PA> q') i (p :: ps) l /\
     stepAt (fun q q' => q -PA- c ;? v -PA> q') j l (p' :: ps'))).
Proof.
  revert p r a. induction ps as [ |q qs IH]; intros p r a H; simpl in H.
  - exists r; exists (@nil ProcTerm). split; [reflexivity | ]. left. exists 0%nat.
    constructor. assumption.
  - apply par_disc_inv in H.
    destruct H as [p0 [q0 [E [[S1 Eq] | [[S2 Ep] | [Et [c [v [[S1 S2] | [S1 S2]]]]]]]]]];
      subst r.
    + subst q0. exists p0; exists (q :: qs). split; [reflexivity | ]. left. exists 0%nat.
      constructor. assumption.
    + subst p0.
      destruct (IH _ _ _ S2) as [q' [qs' [E [[i St] | [Et [i [j [c [v [l [N [S1 S2']]]]]]]]]]]];
        subst q0.
      * exists p; exists (q' :: qs'). split; [reflexivity | ]. left. exists (S i).
        constructor. assumption.
      * exists p; exists (q' :: qs'). split; [reflexivity | ]. right. split; [assumption | ].
        exists (S i); exists (S j); exists c; exists v; exists (p :: l). split; [lia | ].
        split; constructor; assumption.
    + subst a. destruct (IH _ _ _ S2) as [q' [qs' [E [[i St] | [Et _]]]]]; [ | discriminate].
      subst q0. exists p0; exists (q' :: qs'). split; [reflexivity | ]. right.
      split; [reflexivity | ].
      exists 0%nat; exists (S i); exists c; exists v; exists (p0 :: q :: qs).
      split; [discriminate | ]. split; constructor; assumption.
    + subst a. destruct (IH _ _ _ S2) as [q' [qs' [E [[i St] | [Et _]]]]]; [ | discriminate].
      subst q0. exists p0; exists (q' :: qs'). split; [reflexivity | ]. right.
      split; [reflexivity | ].
      exists (S i); exists 0%nat; exists c; exists v; exists (p :: q' :: qs').
      split; [discriminate | ]. split; constructor; assumption.
Qed.

(** A parallel composition delays by every component delaying.*)
Lemma parAll_del_inv p ps d r : parAll p ps -PD- d -PD> r ->
  exists p' ps', r = parAll p' ps' /\
  Forall2 (fun q q' => q -PD- d -PD> q') (p :: ps) (p' :: ps').
Proof.
  revert p r. induction ps as [ |q qs IH]; intros p r H; simpl in H.
  - exists r; exists (@nil ProcTerm). split; [reflexivity | ].
    constructor; [assumption | constructor].
  - apply par_del_inv in H. destruct H as [p' [q0 [E [S1 S2]]]]. subst r.
    destruct (IH _ _ S2) as [q' [qs' [E F]]]. subst q0.
    exists p'; exists (q' :: qs'). split; [reflexivity | ]. constructor; assumption.
Qed.

(** While a parallel composition delays, no two of its components offer complementary
actions.*)
Lemma parAll_del_sort_not p ps d r i j qi qj a : parAll p ps -PD- d -PD> r ->
  i <> j -> nth_error (p :: ps) i = Some qi -> nth_error (p :: ps) j = Some qj ->
  sort a d qi -> ~ sort (a^) d qj.
Proof.
  revert p r i j. induction ps as [ |q qs IH]; intros p r i j H N Ni Nj Si Sj.
  - destruct i as [ |i]; destruct j as [ |j]; simpl in *;
      try (destruct i; discriminate); try (destruct j; discriminate).
    apply N. reflexivity.
  - simpl in H. inversion H as [ | | | | | | ? ? ? ? ? S1 S2 K | | | | ]; subst.
    destruct i as [ |i]; destruct j as [ |j]; simpl in Ni, Nj.
    + exfalso. apply N. reflexivity.
    + injection Ni as Ni. subst qi. apply (K a Si).
      eapply parAll_sort_intro; [ | exact Sj]. eapply nth_error_In. exact Nj.
    + injection Nj as Nj. subst qj. apply (K (a^) Sj). rewrite complementInvol.
      eapply parAll_sort_intro; [ | exact Si]. eapply nth_error_In. exact Ni.
    + eapply IH; [exact S2 | | exact Ni | exact Nj | exact Si | exact Sj].
      intro E. apply N. f_equal. assumption.
Qed.

(** No delay while two components can synchronise.*)
Lemma parAll_del_sync_not p ps d r i j qi qj a : parAll p ps -PD- d -PD> r ->
  i <> j -> nth_error (p :: ps) i = Some qi -> nth_error (p :: ps) j = Some qj ->
  discActEnabled qi a -> discActEnabled qj (a^) -> a <> tauAct -> False.
Proof.
  intros H N Ni Nj Di Dj T.
  apply (parAll_del_sort_not p ps d r i j qi qj a H N Ni Nj);
    apply enabledInSort; try assumption. apply complementNotTau. assumption.
Qed.

(** A discrete step changes each component by at most one step.*)
Lemma parAll_disc_weak p ps a r : parAll p ps -PA- a -PA> r ->
  exists p' ps', r = parAll p' ps' /\
  Forall2 (fun q q' => q = q' \/ exists b, q -PA- b -PA> q') (p :: ps) (p' :: ps').
Proof.
  intro H. apply parAll_disc_inv in H.
  destruct H as [p' [ps' [E [[i St] | [Et [i [j [c [v [l [N [S1 S2]]]]]]]]]]]]; subst r;
    exists p'; exists ps'; (split; [reflexivity | ]).
  - eapply Forall2_impl; [ | eapply stepAt_Forall2; exact St].
    simpl. intros q q' [E | T]; eauto.
  - eapply Forall2_impl; [ | eapply stepAt_stepAt_Forall2; eassumption].
    simpl. intros q q' [E | [T | T]]; eauto.
Qed.

(** A step that is not silent is a step of exactly one component.*)
Lemma parAll_disc_nonTau p ps a r : parAll p ps -PA- a -PA> r -> a <> tauAct ->
  exists p' ps' i, r = parAll p' ps' /\
  stepAt (fun q q' => q -PA- a -PA> q') i (p :: ps) (p' :: ps').
Proof.
  intros H N. apply parAll_disc_inv in H.
  destruct H as [p' [ps' [E [[i St] | [Et _]]]]]; [ | exfalso; apply N; assumption].
  exists p'; exists ps'; exists i. auto.
Qed.

(** Compositions of as many components are the same term only when their components are.*)
Lemma parAll_inj p ps q qs : parAll p ps = parAll q qs -> length ps = length qs ->
  p = q /\ ps = qs.
Proof.
  revert p q qs. induction ps as [ |p2 ps IH]; intros p q qs E L;
    destruct qs as [ |q2 qs]; simpl in *; try discriminate.
  - split; [exact E | reflexivity].
  - injection E as E1 E2. injection L as L. destruct (IH _ _ _ E2 L) as [E3 E4].
    subst. split; reflexivity.
Qed.

(*********Reachability*********)

(** The processes reachable from p0 by any number of discrete steps and delays.*)
Inductive reachableFrom (p0 : ProcTerm) : ProcTerm -> Prop :=
  | reachableFromBase : reachableFrom p0 p0
  | reachableFromDisc p p' a : reachableFrom p0 p -> p -PA- a -PA> p' -> reachableFrom p0 p'
  | reachableFromDel p p' d : reachableFrom p0 p -> p -PD- d -PD> p' -> reachableFrom p0 p'.

(** A property of p0 that every discrete step and every delay preserves holds of everything
reachable from p0.*)
Lemma reachableFrom_invariant (P : ProcTerm -> Prop) p0 p : P p0 ->
  (forall q q' a, P q -> q -PA- a -PA> q' -> P q') ->
  (forall q q' d, P q -> q -PD- d -PD> q' -> P q') ->
  reachableFrom p0 p -> P p.
Proof.
  intros H0 HD HT R. induction R; eauto.
Qed.

(** What is reachable from a process reachable from p0 is reachable from p0.*)
Lemma reachableFrom_trans p0 p q : reachableFrom p0 p -> reachableFrom p q -> reachableFrom p0 q.
Proof. intros R1 R2. induction R2; eauto using reachableFromDisc, reachableFromDel. Qed.

(** What is reachable from a parallel composition is a parallel composition of processes
reachable from its components.*)
Lemma reachableFrom_parAll p0 ps0 q : reachableFrom (parAll p0 ps0) q ->
  exists p ps, q = parAll p ps /\ Forall2 reachableFrom (p0 :: ps0) (p :: ps).
Proof.
  intro R. induction R as [ | q q' a R [p [ps [E F]]] S | q q' d R [p [ps [E F]]] S].
  - exists p0; exists ps0. split; [reflexivity | ].
    apply Forall2_diag. intros. apply reachableFromBase.
  - subst q. apply parAll_disc_weak in S.
    destruct S as [p' [ps' [E G]]]. subst q'. exists p'; exists ps'. split; [reflexivity | ].
    eapply Forall2_impl; [ | eapply Forall2_compose; [exact F | exact G]].
    simpl. intros x z [y [Rxy [Ey | [b T]]]]; subst; eauto using reachableFromDisc.
  - subst q. apply parAll_del_inv in S.
    destruct S as [p' [ps' [E G]]]. subst q'. exists p'; exists ps'. split; [reflexivity | ].
    eapply Forall2_impl; [ | eapply Forall2_compose; [exact F | exact G]].
    simpl. intros x z [y [Rxy T]]. eauto using reachableFromDel.
Qed.

(*********Channels*********)

(** The channel of a discrete action, and the direction the action uses it in.*)
Definition actChan (a : DiscAct) : option (Channel * Direction) :=
  match a with
  | c ;? _ => Some (c, read)
  | c ;! _ => Some (c, write)
  | tauAct => None
  end.

(** The channels of a term's prefixes, with their directions, not looking inside
applications.*)
Fixpoint chansProc (p : ProcTerm) : list (Channel * Direction) :=
  match p with
  | nilProc => []
  | outPrefix c _ _ => [(c, write)]
  | inPrefix c _ _ => [(c, read)]
  | ifThen _ q => chansProc q
  | sum q1 q2 => chansProc q1 ++ chansProc q2
  | parComp q1 q2 => chansProc q1 ++ chansProc q2
  | app _ _ => []
  | del _ q => chansProc q
  end.

(** A term whose applications are all under a prefix acts only on the channels of its
prefixes. So two terms are not bisimilar when one can act on a channel the other does not
mention.*)
Lemma step_chans p a q : p -PA- a -PA> q -> unguardedNames p = [] ->
  forall cd, actChan a = Some cd -> In cd (chansProc p).
Proof.
  intros S U cd E. induction S; simpl in *; try discriminate;
    try (apply app_eq_nil in U; destruct U as [U1 U2]);
    try (injection E as E; subst; left; reflexivity); auto using in_or_app.
Qed.

(** The channels that appear in p as written, each with the direction it is used in. The body
of a name that p applies is not part of p.*)
Fixpoint prefixChans (p : ProcTerm) : list (Channel * Direction) :=
  match p with
  | nilProc => []
  | outPrefix c _ q => (c, write) :: prefixChans q
  | inPrefix c _ q => (c, read) :: prefixChans q
  | ifThen _ q => prefixChans q
  | sum q1 q2 => prefixChans q1 ++ prefixChans q2
  | parComp q1 q2 => prefixChans q1 ++ prefixChans q2
  | app _ _ => []
  | del _ q => prefixChans q
  end.

(** Substitution keeps the channels of a term's prefixes.*)
Lemma prefixChans_sub s p : prefixChans (subProcTerm s p) = prefixChans p.
Proof.
  revert s. induction p; intro s; simpl; try rewrite IHp; try rewrite IHp1, IHp2; reflexivity.
Qed.

(** Helper for prefixChans_reachableFrom: a discrete step acts on a channel and direction that
P allows, and leads to a term whose prefixes P allows, when P allows the prefixes of the term
and of every definition.*)
Local Lemma prefixChans_reachableFrom_aux (P : Channel * Direction -> Prop) p a p' :
  (forall n, Forall P (prefixChans (snd (def n)))) -> Forall P (prefixChans p) ->
  p -PA- a -PA> p' -> Forall P (prefixChans p') /\ forall cd, actChan a = Some cd -> P cd.
Proof.
  intros D F S. revert F.
  induction S as [c l1 l2 p E | c l1 l2 p E | b p p' d S IH E | p1 p2 p' d S IH
    | p1 p2 p' d S IH | p p' q d S IH | q q' p d S IH | p p' q q' c l S1 IH1 S2 IH2
    | p p' q q' c l S1 IH1 S2 IH2 | n l1 l2 p p' d E S IH | p p' d e S IH E];
    intro F; simpl in F |- *; Forall_app_split.
  - inversion F; subst. split; [assumption | intros cd X; injection X as X; subst; assumption].
  - inversion F; subst. rewrite prefixChans_sub.
    split; [assumption | intros cd X; injection X as X; subst; assumption].
  - apply IH. exact F.
  - apply IH. assumption.
  - apply IH. assumption.
  - destruct IH as [F' A]; [assumption | ]. split; [apply Forall_app; split | ]; assumption.
  - destruct IH as [F' A]; [assumption | ]. split; [apply Forall_app; split | ]; assumption.
  - split; [apply Forall_app; split; [apply IH1 | apply IH2]; assumption | discriminate].
  - split; [apply Forall_app; split; [apply IH1 | apply IH2]; assumption | discriminate].
  - apply IH. rewrite prefixChans_sub. specialize (D n). rewrite E in D. exact D.
  - apply IH. exact F.
Qed.

(** Helper for prefixChans_reachableFrom: a delay leads to a term whose prefixes P allows, when
P allows the prefixes of the term and of every definition.*)
Local Lemma prefixChans_reachableFrom_aux2 (P : Channel * Direction -> Prop) p d p' :
  (forall n, Forall P (prefixChans (snd (def n)))) -> Forall P (prefixChans p) ->
  p -PD- d -PD> p' -> Forall P (prefixChans p').
Proof.
  intros D F S. revert F.
  induction S as [ | | | p p' d b S IH E | | p1 p2 p1' p2' d S1 IH1 S2 IH2
    | p q p' q' d S1 IH1 S2 IH2 K | n l1 l2 p p' d E S IH | | | ];
    intro F; simpl in F |- *; Forall_app_split; try (apply Forall_app; split); auto.
  apply IH. rewrite prefixChans_sub. specialize (D n). rewrite E in D. exact D.
Qed.

(** A property of channels and directions that every prefix of p0 has, and every prefix of
every definition, holds of every action of anything reachable from p0.*)
Lemma prefixChans_reachableFrom (P : Channel * Direction -> Prop) p0 p a p' cd :
  Forall P (prefixChans p0) -> (forall n, Forall P (prefixChans (snd (def n)))) ->
  reachableFrom p0 p -> p -PA- a -PA> p' -> actChan a = Some cd -> P cd.
Proof.
  intros F0 D R S E.
  assert (F : Forall P (prefixChans p)).
  { apply (reachableFrom_invariant (fun q => Forall P (prefixChans q)) p0 p F0); [ | | exact R].
    - intros q q' b F' T. exact (proj1 (prefixChans_reachableFrom_aux P q b q' D F' T)).
    - intros q q' d F' T. exact (prefixChans_reachableFrom_aux2 P q d q' D F' T). }
  exact (proj2 (prefixChans_reachableFrom_aux P p a p' D F S) cd E).
Qed.

(*********Correct use of an entity's channels*********)
(** The software meets the rest of its entity on channels that each go one way (chanDir). The
language lets software use any channel either way, but software that uses one of these the
wrong way can meet another of its own components on it, by mistake. Software that uses them
correctly meets only the rest of its entity on them (ent_disc_comp_chan in
EntityLanguage.v).*)

(** Software uses its entity's channels correctly when nothing reachable from it, by discrete
steps or delays, can write on a channel it should read or read one it should write: every
channel it acts on has no direction, or the direction of the action.*)
Definition correctChannelUsage (p : ProcTerm) : Prop :=
  forall q a q' c d, reachableFrom p q -> q -PA- a -PA> q' -> actChan a = Some (c, d) ->
  chanDir c = None \/ chanDir c = Some d.

(** What is reachable from software that uses its channels correctly uses them correctly
too.*)
Lemma correctChannelUsage_reachableFrom p q :
  correctChannelUsage p -> reachableFrom p q -> correctChannelUsage q.
Proof.
  intros C R r a r' c d Rr. apply (C r a r' c d). eapply reachableFrom_trans; eassumption.
Qed.

(** No prefix of p goes the wrong way on its channel.*)
Definition prefixesRightWay (p : ProcTerm) : Prop :=
  Forall (fun '(c, d) => chanDir c = None \/ chanDir c = Some d) (prefixChans p).

(** A syntactic check that software uses its entity's channels correctly: no prefix goes the
wrong way, in the software or in any definition.*)
Lemma correctChannelUsage_prefixes p :
  prefixesRightWay p -> (forall n, prefixesRightWay (snd (def n))) -> correctChannelUsage p.
Proof.
  intros F D q a q' c d R S E. exact (prefixChans_reachableFrom _ _ _ _ _ (c, d) F D R S E).
Qed.

(** Software that uses its channels correctly cannot both write and read one of the entity's
channels.*)
Lemma correctChannelUsage_dir p c v w : correctChannelUsage p ->
  discActEnabled p (c ;! v) -> discActEnabled p (c ;? w) -> chanDir c = None.
Proof.
  intros C [p1 S1] [p2 S2].
  destruct (C p _ _ c write (reachableFromBase p) S1 eq_refl) as [N1 | N1]; [exact N1 | ].
  destruct (C p _ _ c read (reachableFromBase p) S2 eq_refl) as [N2 | N2]; [exact N2 | ].
  congruence.
Qed.

(** An action on one of the channels the software shares with the rest of its entity.*)
Definition entChanAct (b : DiscAct) : Prop :=
  match actChan b with Some (c, _) => chanDir c <> None | None => False end.

(** In a composition that uses its channels correctly, a component that can only have changed
by acting on one of the entity's channels either stayed as it was, or the composition's step
was that component's step, with the same action, every other component staying as it was. It
cannot have synchronised with another component, since one of them would have used the
channel the wrong way.*)
Lemma parAll_disc_chan q qs q' qs' b i x x' :
  correctChannelUsage (parAll q qs) -> parAll q qs -PA- b -PA> parAll q' qs' ->
  length qs = length qs' -> nth_error (q :: qs) i = Some x -> nth_error (q' :: qs') i = Some x' ->
  (forall b', x -PA- b' -PA> x' -> entChanAct b') ->
  x = x' \/ stepAt (fun y y' => y -PA- b -PA> y') i (q :: qs) (q' :: qs').
Proof.
  intros C T L Nx Nx' ACT.
  destruct (parAll_disc_inv _ _ _ _ T)
    as [r [rs [E [[j St] | [_ [j [j' [c [v [l0 [N [S1 S2]]]]]]]]]]]].
  - (* one component steps *)
    assert (LR : length qs' = length rs).
    { pose proof (Forall2_length (stepAt_Forall2 _ _ _ _ St)) as L1. simpl in L1. lia. }
    destruct (parAll_inj _ _ _ _ E LR) as [E1 E2]. subst r rs.
    destruct (Nat.eq_dec i j) as [Ej | Nj]; [subst j; right; exact St | left].
    pose proof (stepAt_nth_error_neq _ _ _ _ _ St Nj). congruence.
  - (* two components synchronise on c, which therefore has no direction *)
    assert (LR : length qs' = length rs).
    { pose proof (Forall2_length (stepAt_Forall2 _ _ _ _ S1)) as L1.
      pose proof (Forall2_length (stepAt_Forall2 _ _ _ _ S2)) as L2. simpl in L1, L2. lia. }
    destruct (parAll_inj _ _ _ _ E LR) as [E1 E2]. subst r rs.
    destruct (stepAt_nth_error_eq _ _ _ _ S1) as [x1 [y1 [N1 [N1' T1]]]].
    destruct (stepAt_nth_error_eq _ _ _ _ S2) as [w1 [z1 [N2 [N2' T2]]]].
    cbv beta in T1, T2.
    assert (N2o : nth_error (q :: qs) j' = Some w1)
      by (rewrite (stepAt_nth_error_neq _ _ _ _ _ S1 (not_eq_sym N)); exact N2).
    assert (DIR : chanDir c = None).
    { apply (correctChannelUsage_dir _ c v v C).
      - apply (parAll_dae_intro _ _ x1); [eapply nth_error_In; exact N1 | econstructor; exact T1].
      - apply (parAll_dae_intro _ _ w1); [eapply nth_error_In; exact N2o | econstructor; exact T2]. }
    destruct (Nat.eq_dec i j) as [Ej | Nj]; [ | destruct (Nat.eq_dec i j') as [Ej' | Nj']].
    + (* the component wrote on c *)
      subst j. exfalso.
      assert (Ey : y1 = x').
      { rewrite (stepAt_nth_error_neq _ _ _ _ _ S2 N) in N1'. congruence. }
      assert (Ex : x1 = x) by congruence. subst x1 y1.
      exact (ACT _ T1 DIR).
    + (* the component read c *)
      subst j'. exfalso.
      assert (Ex : w1 = x) by congruence. assert (Ez : z1 = x') by congruence. subst w1 z1.
      exact (ACT _ T2 DIR).
    + (* the component did neither *)
      left. pose proof (stepAt_nth_error_neq _ _ _ _ _ S1 Nj).
      pose proof (stepAt_nth_error_neq _ _ _ _ _ S2 Nj'). congruence.
Qed.

End Results.

Notation "p1 -P=> p2" := (stepProcRefl p1 p2) (at level 50).
Notation "d %; p" := (minGuard d p).

(** Repeatedly inverts a discrete step from nilProc, an output or input prefix, a sum, a
delay guard or a conditional, clearing it and substituting. The impossible branches
close.*)
Ltac invert_disc_prefixes := repeat match goal with
  | [H : nilProc -PA- _ -PA> _ |- _] => inversion H
  | [H : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; clear H; subst
  | [H : inPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; clear H; subst
  | [H : sum _ _ -PA- _ -PA> _ |- _] => inversion H; clear H; subst
  | [H : del _ _ -PA- _ -PA> _ |- _] => inversion H; clear H; subst
  | [H : ifThen _ _ -PA- _ -PA> _ |- _] => inversion H; clear H; subst
  end.

(** Solves a goal [forall d q, X -PD- d -PD> q -> q = X] for X built from nilProc,
prefixes and sums.*)
Ltac del_self_tac := first [ apply del_self_nil | apply del_self_outPrefix
  | apply del_self_inPrefix | (apply del_self_sum; del_self_tac) ].
