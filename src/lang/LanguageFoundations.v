(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

Require Import ComhCoq.lib.Extras.LibTactics.

(** This file lays down the foundation for the software language file by defining things like expressions and evaluation of expressions.*)

Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
From Stdlib Require Export Relations.
From Stdlib Require Export Lists.ListSet.
From Stdlib Require Export Reals Arith.
From Stdlib Require Export List.
From Stdlib Require Export Logic.FunctionalExtensionality.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.

Open Scope nat_scope.


(** The types of the values of the language: a mode, a time, a position, a distance, a
delay or a non-negative real. Each is the type of the base values built with the matching
constructor of BaseType below.*)
Inductive ValType : Type :=
  vtMode | vtTime | vtPosition | vtDistance | vtDelay | vtNonneg.

(** Equality on value types is decidable.*)
Definition valTypeEqDec (t t' : ValType) : {t = t'} + {t <> t'}.
  decide equality. Defined.

Lemma eqDecValType : eqDec ValType. unfold eqDec. intros.
  destruct (valTypeEqDec x1 x2); [left | right]; assumption. Qed.

(** A countably infinite set of variables of each type, indexed by natural numbers. The
type of a variable is the type of the values an input may bind it to: the variables of an
input prefix are typed, as in the thesis (p.64).*)
Inductive Var : Type :=
  | var : ValType -> nat -> Var.

(** The type of a variable.*)
Definition varType (x : Var) : ValType :=
  match x with var t _ => t end.

Lemma eqDecVar : eqDec Var. unfold eqDec. destruct x1 as [t n], x2 as [t' n'].
  destruct (valTypeEqDec t t') as [E | NE];
    [subst t' | right; intro H; apply NE; inversion H; reflexivity].
  destruct (eq_nat_dec n n') as [E | NE];
    [subst n'; left; reflexivity | right; intro H; apply NE; inversion H; reflexivity].
  Qed.

(** BaseType type elements are either a mode, a time, a position, a distance or a delay.
We use coercions to reduce constructor verbosity.*)
Inductive BaseType : Type:=
  | baseMode :> Mode -> BaseType
  | baseTime :> Time -> BaseType
  | basePosition :> Position -> BaseType
  | baseDistance :> Distance -> BaseType
  | baseDelay :> Delay -> BaseType
  | baseNonneg :> nonnegreal -> BaseType.

(** Equality on the base type is decidable.*)
Lemma eqDecBase : eqDec BaseType. unfold eqDec. unfold decidable.
  intros. destruct x1, x2; try solve [right; unfold not; intros; inversion H].
  addHyp (eqDecMode m m0). invertClear H. rewrite H0. left. reflexivity.
  right. unfold not. intros. apply H0. invertClear H. reflexivity.
  addHyp (eqDecTime t t0). invertClear H. rewrite H0. left. reflexivity.
  right. unfold not. intros. apply H0. invertClear H. reflexivity. 
  addHyp (eqDecPosition p p0). invertClear H. rewrite H0. left. reflexivity.
  right. unfold not. intros. apply H0. invertClear H. reflexivity.   
  addHyp (eqDecDistance d d0). invertClear H. rewrite H0. left. reflexivity.
  right. unfold not. intros. apply H0. invertClear H. reflexivity.  
  addHyp (eqDecDelay d d0). invertClear H. rewrite H0. left. reflexivity.
  right. unfold not. intros. apply H0. invertClear H. reflexivity. 
  addHyp (eqDecNonnegReal n n0). invertClear H. rewrite H0. left. reflexivity.
  right. unfold not. intros. apply H0. invertClear H. reflexivity. Qed.

(** The type of a base value.*)
Definition valTypeOf (b : BaseType) : ValType :=
  match b with
  | baseMode _ => vtMode
  | baseTime _ => vtTime
  | basePosition _ => vtPosition
  | baseDistance _ => vtDistance
  | baseDelay _ => vtDelay
  | baseNonneg _ => vtNonneg
  end.

(** A value of type mode is a mode, and likewise for the other types.*)
Lemma valTypeOf_mode b : valTypeOf b = vtMode -> exists m, b = baseMode m.
  destruct b; simpl; intro H; inversion H. eexists. reflexivity. Qed.

Lemma valTypeOf_time b : valTypeOf b = vtTime -> exists t, b = baseTime t.
  destruct b; simpl; intro H; inversion H. eexists. reflexivity. Qed.

Lemma valTypeOf_position b : valTypeOf b = vtPosition -> exists l, b = basePosition l.
  destruct b; simpl; intro H; inversion H. eexists. reflexivity. Qed.

Lemma valTypeOf_distance b : valTypeOf b = vtDistance -> exists r, b = baseDistance r.
  destruct b; simpl; intro H; inversion H. eexists. reflexivity. Qed.

(** The values vs are typed for the variables xs: there is one value per variable, and each
value has its variable's type. An input binds its variables only to such values, so a
process never holds a time where it expects a mode.*)
Definition typedVals (xs : list Var) (vs : list BaseType) : Prop :=
  Forall2 (fun x v => valTypeOf v = varType x) xs vs.

(** Typed values are exactly the value lists whose types are the variables' types.*)
Lemma typedVals_map xs vs : typedVals xs vs <-> map valTypeOf vs = map varType xs.
  unfold typedVals. split.
  - intro H. induction H; simpl; [reflexivity | f_equal; assumption].
  - revert vs. induction xs as [ | x xs IH]; intros vs E; destruct vs as [ | v vs];
    simpl in E; try discriminate; constructor; inversion E; auto.
  Qed.

Lemma typedVals_length xs vs : typedVals xs vs -> length vs = length xs.
  intro H. apply Forall2_length in H. symmetry. assumption. Qed.

Lemma typedVals_dec xs vs : {typedVals xs vs} + {~typedVals xs vs}.
  destruct (list_eq_dec valTypeEqDec (map valTypeOf vs) (map varType xs)) as [E | NE].
  - left. apply typedVals_map. assumption.
  - right. intro H. apply NE. apply typedVals_map. assumption.
  Qed.

(** Inversion of typed values on the shape of the variable list.*)
Lemma typedVals_nil_inv vs : typedVals [] vs -> vs = [].
  intro H. inversion H. reflexivity. Qed.

Lemma typedVals_cons_inv x xs vs : typedVals (x :: xs) vs ->
  exists v vs', vs = v :: vs' /\ valTypeOf v = varType x /\ typedVals xs vs'.
  intro H. inversion H; subst. eauto. Qed.


(** A simple expression language over the base types.*)
Inductive Exp : Type :=
  | eVar :> Var -> Exp
  | eBase :> BaseType -> Exp
  | eSubtract : Exp -> Exp -> Exp
  | eAdd : Exp -> Exp -> Exp
  | eMult : Exp -> Exp -> Exp
  | eWaitTime : Exp -> Exp -> Exp
  | ePeriod : Exp -> Exp
  | eDist : Exp -> Exp -> Exp
  | eFailSafeSucc : Exp -> Exp.

(** Equality is decidable on expressions.*)
Lemma eqDecExp : eqDec Exp. unfold eqDec. induction x1;
  induction x2; try solve [right; unfold not; intros; inversion H];
  try solve [addHyp (IHx1_1 x2_1); invertClear H; [rewrite H0;
  addHyp (IHx1_2 x2_2); invertClear H; [rewrite H1;
  left; f_equal | right; unfold not; intros; apply H1;
  inversion H; reflexivity] | right; unfold not; intros; apply H0;
  inversion H; reflexivity]]; try solve [addHyp (IHx1 x2); invertClear H;
  [left; rewrite H0; reflexivity | right; unfold not; intros;
  apply H0; inversion H; reflexivity]]. 
  addHyp (eqDecVar v v0). invertClear H. left. rewrite H0. reflexivity.
  right. unfold not. intros. apply H0. inversion H. reflexivity.
  addHyp (eqDecBase b b0). invertClear H. left. rewrite H0. reflexivity.
  right. unfold not. intros. apply H0. inversion H. reflexivity. Qed.



(** A set of channels. Each mode-state channel comes in two: the software
  reads from one and writes to the other, so its direction is in its name.*)
Inductive Channel : Type :=
  chanAN | chanMStableRead | chanMStableWrite | chanMCurrRead | chanMCurrWrite
  | chanMNextRead | chanMNextWrite
  | chanPos | chanOutProc | chanInProc | chanIOEnv | chanTrans
  | chanWake | chanPause | chanUnpause | chanBad
  | chanAbort.

(** Equality on channels is decidable.*)
Lemma eqDecChannel : eqDec Channel. unfold eqDec.
  destruct x1, x2; try solve [right; unfold not; intros; inversion H];
  left; reflexivity. Qed.


(** A substitution is a mapping from variables to expressions.*)
Definition Subst := Var -> Exp.

(** The id substitution simply lifts every variable to an expression i.e. it
maps every variable to itself, with the eVar constructor as a wrapper.*)
Definition idSubst (v : Var) : Exp :=
  (eVar v).

(**Maps the function s over e, replacing all variables with their
corresponding expression..*)
Fixpoint subExp (s : Subst) (e : Exp) : Exp :=
  match e with
  | eVar v => s v
  | eBase b => eBase b
  | eSubtract e1 e2 => eSubtract (subExp s e1) (subExp s e2)
  | eAdd e1 e2 => eAdd (subExp s e1) (subExp s e2)
  | eMult e1 e2 => eMult (subExp s e1) (subExp s e2)
  | eWaitTime e1 e2 => eWaitTime (subExp s e1) (subExp s e2)
  | ePeriod e' => ePeriod (subExp s e')
  | eDist e1 e2 => eDist (subExp s e1) (subExp s e2)
  | eFailSafeSucc e1 => eFailSafeSucc (subExp s e1)
  end.

(**If one number is less than another, then they are not equal.*)
Lemma lt_neq_nat : forall n m : nat,
  n < m -> n <> m.
  induction n. destruct m. intros. inversion H.
  intros. unfold not. intros. inversion H0.
  intros. apply Nat.lt_succ_lt_pred in H. destruct m. inversion H.
  simpl in H. apply IHn in H. unfold not. intros. apply H.
  inversion H0. reflexivity. Qed.

(**Given any two numbers, they are either equal or not.*)
Lemma natDec : forall n m : nat,
  {n = m} + {n <> m}. intros.
  assert ({n < m} + {n = m} + {m < n}).
  apply lt_eq_lt_dec. inversion H.
  inversion H0. apply lt_neq_nat in H1. right. apply H1.
  left. apply H1. right. apply lt_neq_nat in H0. unfold not.
  intros. apply H0. symmetry. assumption. Qed.

(**Given any two variables, they are either equal or not.*)
Lemma varEqDec : forall x y : Var, {x = y} + {x <> y}.
  decide equality; first [apply natDec | apply valTypeEqDec]. Qed.

(**True if the arguments are equal, false otherwise.*)
Definition varEq (v1 v2 : Var) : bool :=
  match (varEqDec v1 v2) with
  | left _ => true
  | right _ => false
  end.

(**Stolen from tutorial. Takes any function with domain Var and overrides
it with a new v -> x pair.*)
Definition update {X : Type} (f : Var -> X) (v : Var) (x : X) : (Var -> X) :=
  fun v' => if (varEq v v') then x else (f v').

(**Turns a pair of lists lv : [variables] le : [expressions] into a substitution function
from variables to expressions which is the identity at all points except those in lv,
which are mapped to their corresponding element of le. Note: If values are repeated in lv,
then earlier values override later ones.*)
Fixpoint listsToSub (lv : list Var) (lex : list Exp) : Subst :=
  match lv , lex with
  | v :: lv' , e :: lex' => (update (listsToSub lv' lex') v e)
  | [] , _ :: _ => idSubst
  | _ , [] => idSubst
  end.

(**Applies the substitution to each element of the list.*)
Definition listSub (s : Subst) (l : list Exp) : list Exp :=
  map (subExp s) l.

(**Is the variable v in the list lv.*)
Fixpoint inVarList (v : Var) (lv : list Var) : bool :=
  match lv with
  | [] => false
  | v' :: lv' => if (varEq v v') then true else (inVarList v lv')
  end.

(**Resets all the variables in lv to map to themselves.*)
Definition resetSub (s : Subst) (lv : list Var) (v : Var) : Exp :=
  match (inVarList v lv) with
  | true => eVar v
  | false => s v
  end.

Open Scope R_scope.

(** Evaluates certain base values (Delay, Time, Distance, Nonneg) to nonnegative reals.
Used to "normalise" the types of things so that +, - and * can be computed over
expressions.*)
Inductive evalBaseNonneg : BaseType -> nonnegreal -> Prop :=
  | ebnDel r : evalBaseNonneg (baseDelay (mkDelay r)) (posToNonneg r)
  | ebnTime r : evalBaseNonneg (baseTime (mkTime r)) r
  | ebnDistance r : evalBaseNonneg (baseDistance (mkDistance r)) r
  | ebnNonneg r : evalBaseNonneg (baseNonneg r) r.
Notation "b \_/ r" := (evalBaseNonneg b r) (at level 45).

Lemma evalBaseNonneg_unique b r1 r2 :
  b \_/ r1 -> b \_/ r2 -> r1 = r2. intros.
  inversion H; inversion H0; inversion H3; subst;
  inversion H5; reflexivity. Qed.

Definition evalBaseNonnegFun (b : BaseType) : option nonnegreal :=
  match b with
  | baseDelay (mkDelay r) => Some (posToNonneg r)
  | baseTime (mkTime r) => Some r
  | baseDistance (mkDistance r) => Some r
  | baseNonneg r => Some r
  | _ => None
  end.

Lemma evalBaseNonneg_rel_fun b r :
  b \_/ r -> evalBaseNonnegFun b = Some r.
  intros. inversion H; simpl; reflexivity. Qed.

Lemma evalBaseNonneg_fun_rel b r :
  evalBaseNonnegFun b = Some r -> b \_/ r.
  intros. destruct b; inversion H; simpl;
  match goal with |- ?f ?x \_/ _ =>
  destruct x end; inversion H1; constructor. Qed.

(**Evaluation on terms of Exp. Note that only closed terms will actually evaluate to
something. If we can prove evalExp e b then e evaluates to b.*)
Inductive evalExp : Exp -> BaseType -> Prop :=
  | evalBase : forall b : BaseType, evalExp (eBase b) b
  | evalSub : forall (e1 e2 : Exp) (b1 b2 : BaseType) (r1 r2 : nonnegreal),
  evalExp e1 b1 -> evalExp e2 b2 -> b1 \_/ r1 -> b2 \_/ r2 ->
  evalExp (eSubtract e1 e2) (r1 -nn- r2)
  | evalAdd : forall (e1 e2 : Exp) (b1 b2 : BaseType) (r1 r2 : nonnegreal),
  evalExp e1 b1 -> evalExp e2 b2 -> b1 \_/ r1 -> b2 \_/ r2 ->
  evalExp (eAdd e1 e2) (r1 +nn+ r2)
  | evalMult : forall (e1 e2 : Exp) (b1 b2 : BaseType) (r1 r2 : nonnegreal),
  evalExp e1 b1 -> evalExp e2 b2 -> b1 \_/ r1 -> b2 \_/ r2 ->
  evalExp (eMult e1 e2) (r1 *nn* r2)
  | evalWait : forall (e1 e2 : Exp) (m1 : Mode) (m2 : Mode)
  (p : m1 -mtr-> m2), evalExp e1 m1 -> evalExp e2 m2 -> 
  evalExp (eWaitTime e1 e2) (waitTime m1 m2 p)
  | evalPeriod : forall (e : Exp) (m : Mode), evalExp e m ->
  evalExp (ePeriod e) (period m)
  | evalDist : forall (e1 e2 : Exp) (p1 p2 : Position),
  evalExp e1 p1 -> evalExp e2 p2 -> 
  evalExp (eDist e1 e2) (mkDistance (dist2d p1 p2))
  | evalFailSafeSucc : forall (e : Exp) (m : Mode),
  evalExp e m -> evalExp (eFailSafeSucc e) (failSafeSucc m).
Notation "e |_| b" := (evalExp e b) (at level 50).

(** Option map function for two arguments.*)
Definition optionMap2 {A B C : Type} (f : A -> B -> C)
  (a : option A) (b : option B) : option C :=
  match (option_map f a) with
  | Some g => option_map g b
  | None => None
  end.

(** A functional encoding of the evaluation relation as a partial function. The
proof that the two coincide is a separate issue! This function, due to its dealings
with the horrid option type, is quite ugly and hard to understand, but its advantage
is its computability. Once it is linked to the relation via proofs, it can be left as
an under the hood engine that "computes" the relation.*)
Fixpoint evalExpFun (e : Exp) : option BaseType :=
  match e with
  | eVar v => None
  | eBase b => Some b
  | eSubtract e1 e2 =>
    match (evalExpFun e1), (evalExpFun e2) with
    | Some b1, Some b2 =>
      match (evalBaseNonnegFun b1), (evalBaseNonnegFun b2) with
      | Some r1, Some r2 => Some (baseNonneg (r1 -nn- r2))
      | _, _ => None
      end
    | _, _ => None
    end
  | eAdd e1 e2 =>
    match (evalExpFun e1), (evalExpFun e2) with
    | Some b1, Some b2 =>
      match (evalBaseNonnegFun b1), (evalBaseNonnegFun b2) with
      | Some r1, Some r2 => Some (baseNonneg (r1 +nn+ r2))
      | _, _ => None
      end
    | _, _ => None
    end
  | eMult e1 e2 =>
    match (evalExpFun e1), (evalExpFun e2) with
    | Some b1, Some b2 =>
      match (evalBaseNonnegFun b1), (evalBaseNonnegFun b2) with
      | Some r1, Some r2 => Some (baseNonneg (r1 *nn* r2))
      | _, _ => None
      end
    | _, _ => None
    end

  | eWaitTime e1 e2 =>
    match (evalExpFun e1), (evalExpFun e2) with
    | Some b1, Some b2 =>
      match b1, b2 with
      | baseMode m1, baseMode m2 => option_map baseTime
        (option_map (waitTime m1 m2) (modeTransRelOpt m1 m2))
      | _, _ => None
      end
    | _, _ => None
    end 
  | ePeriod e' =>
    match (evalExpFun e') with
    | Some b =>
      match b with
      | baseMode m => Some (baseTime (period m))
      | _ => None
      end
    | None => None
    end
  | eDist e1 e2 =>
    match (evalExpFun e1), (evalExpFun e2) with
    | Some b1, Some b2 =>
      match b1, b2 with
      | basePosition p1, basePosition p2 =>
        Some (baseDistance ((mkDistance (dist2d p1 p2))))
      | _, _ => None
      end
    | _, _ => None
    end
  | eFailSafeSucc e' =>
    match (evalExpFun e') with
    | Some b =>
      match b with
      | baseMode m => Some (baseMode (failSafeSucc m))
      | _ => None
      end
    | None => None
    end
  end.

(*LOCAL TIDY*)

Ltac evalBaseNonneg_rel_fun_step := match goal with
  [V : _ \_/ _ |- _] => apply evalBaseNonneg_rel_fun in V end.

Ltac evalBaseNonneg_rel_fun_tac := repeat evalBaseNonneg_rel_fun_step.

Ltac evalBaseNonneg_fun_rel_step := match goal with
  [V : Some _ = evalBaseNonnegFun _ |- _] => symmetry in V;
  apply evalBaseNonneg_fun_rel in V end.

Ltac evalBaseNonneg_fun_rel_tac := repeat evalBaseNonneg_fun_rel_step.

(*-LOCAL TIDY*)

(** If e evaluates to b via the evaluation relation then it does so also by the evalution
function.*)
Theorem evalExpRelFun : forall (e : Exp) (b : BaseType),
  evalExp e b -> evalExpFun e = Some b. intros.
  induction H; simpl; try rewrite IHevalExp;
  try rewrite IHevalExp1; try rewrite IHevalExp2;
  unfold option_map; try rewrite H1; simpl; try reflexivity; try
  (evalBaseNonneg_rel_fun_tac; rewrite H1; rewrite H2; reflexivity).
  unfold modeTransRelOpt. destruct (modeTransRelDec m1 m2).
  simpl. repeat f_equal. apply proof_irrelevance.
  false. Qed.

(** If e evaluates to b via the evaluation function then it does so
also by the evalution relation.*)
Theorem evalExpFunRel : forall (e : Exp) (b : BaseType),
  evalExpFun e = Some b -> evalExp e b. intros. generalize dependent b.
  induction e; intros. inversion H. inversion H. constructor. 
  (** Subtract case.*)
  inversion H.
  remember (evalExpFun e1) as ev1. remember (evalExpFun e2) as ev2.
  destruct ev1, ev2; try solve [inversion H1].
  remember (evalBaseNonnegFun b0) as bv0. remember (evalBaseNonnegFun b1) as bv1.
  destruct bv0, bv1; try solve [inversion H1]. evalBaseNonneg_fun_rel_tac.  
  inversion H1. econstructor; [eapply IHe1; reflexivity |
  eapply IHe2; reflexivity | | ]; assumption.
  (** Add case.*)
  inversion H.
  remember (evalExpFun e1) as ev1. remember (evalExpFun e2) as ev2.
  destruct ev1, ev2; try solve [inversion H1].
  remember (evalBaseNonnegFun b0) as bv0. remember (evalBaseNonnegFun b1) as bv1.
  destruct bv0, bv1; try solve [inversion H1]. evalBaseNonneg_fun_rel_tac.  
  inversion H1. econstructor; [eapply IHe1; reflexivity |
  eapply IHe2; reflexivity | | ]; assumption.
  (** Multiply case.*)
  inversion H.
  remember (evalExpFun e1) as ev1. remember (evalExpFun e2) as ev2.
  destruct ev1, ev2; try solve [inversion H1].
  remember (evalBaseNonnegFun b0) as bv0. remember (evalBaseNonnegFun b1) as bv1.
  destruct bv0, bv1; try solve [inversion H1]. evalBaseNonneg_fun_rel_tac.  
  inversion H1. econstructor; [eapply IHe1; reflexivity |
  eapply IHe2; reflexivity | | ]; assumption.
  (** waitTime case.*)
  inversion H. remember (evalExpFun e1) as ev1. remember (evalExpFun e2) as ev2.
  destruct ev1, ev2. addHyp (IHe1 b0 (eq_refl (Some b0))).
  addHyp (IHe2 b1 (eq_refl (Some b1))). clear IHe1 IHe2.
  destruct b0, b1; try solve [inversion H1]. unfold option_map in H1.
  remember (modeTransRelOpt m m0) as s. destruct s. inversion H1.
  constructor; assumption. inversion H1. inversion H1. inversion H1.
  inversion H1.
  (** period case.*)
  inversion H. remember (evalExpFun e) as ev. destruct ev.
  addHyp (IHe b0 (eq_refl (Some b0))). clear IHe.
  destruct b0; inversion H1. constructor. assumption. inversion H1.
  (** distance case.*)
  inversion H. remember (evalExpFun e1) as ev1. remember (evalExpFun e2) as ev2.
  destruct ev1, ev2. addHyp (IHe1 b0 (eq_refl (Some b0))).
  addHyp (IHe2 b1 (eq_refl (Some b1))). clear IHe1 IHe2.
  destruct b0, b1; try solve [inversion H1]. unfold option_map in H1.
  inversion H1. constructor; assumption. inversion H1. inversion H1.
  inversion H1.
  (** failSafeSucc case.*)
  inversion H. remember (evalExpFun e) as ev. destruct ev.
  addHyp (IHe b0 (eq_refl (Some b0))). clear IHe.
  destruct b0; inversion H1. constructor. assumption. inversion H1.
  Qed.

(** A function that tries to evaluate the expression e into a time or fails.*)
Definition evalExpFunTime (e : Exp) : option Time :=
  match evalExpFun e with
  | Some b => match evalBaseNonnegFun b with
    | Some r => Some (mkTime r)
    | None => None end
  | _ => None
  end.

Lemma evalExpFunTime_some (e : Exp) (t : Time) :
  evalExpFunTime e = Some t -> exists b, evalExpFun e = Some b.
Proof.
  unfold evalExpFunTime. destruct (evalExpFun e) as [b | ]; [ | discriminate].
  intros _. exists b. reflexivity.
Qed.

Lemma evalExpFunTime_period (m : Mode) : evalExpFunTime (ePeriod m) = Some (period m).
Proof. unfold evalExpFunTime. simpl. destruct (period m) as [r]. reflexivity. Qed.

(** Subtracting the period of a mode from a time expression gives the truncated difference.*)
Lemma evalExpFunTime_subtract_period (m : Mode) (e : Exp) (t : Time) :
  evalExpFunTime e = Some t ->
  evalExpFunTime (eSubtract e (ePeriod m)) = Some (mkTime (time t -nn- time (period m))).
Proof.
  unfold evalExpFunTime. simpl. destruct (evalExpFun e) as [b | ]; [ | discriminate].
  destruct (evalBaseNonnegFun b) as [r | ]; [ | discriminate].
  intro E. injection E as E. subst t. destruct (period m) as [r2]. simpl. reflexivity.
Qed.

(**List the eval relation to work between lists of expressions and lists of values.
l1 l2 is a member of this relation iff the ith element of l1 evaluates to the ith element
of l2 for all i.*)
Inductive evalExpLists : list Exp -> list BaseType -> Prop :=
  | evalElNil : evalExpLists [] []
  | evalElCons : forall (e : Exp) (b : BaseType) (l1 : list Exp) (l2 : list BaseType),
    evalExp e b -> evalExpLists l1 l2 -> evalExpLists (e :: l1) (b :: l2).

(**Convert a list of base values to a list of expressions.*)
Definition listBaselistExp (l1 : list BaseType) : list Exp :=
  map eBase l1.

Inductive BoolExp : Type := 
  | bSufficient : Exp -> Exp -> BoolExp
  | bNot : BoolExp -> BoolExp
  | bEqual : Exp -> Exp -> BoolExp
  | bPossInc : Exp -> Exp -> Exp -> BoolExp.

(** Equality is decidable on boolean expressions.*)
Lemma eqDecBoolExp : eqDec BoolExp. unfold eqDec.
  induction x1; induction x2; try solve [addHyp (eqDecExp e e1);
  addHyp (eqDecExp e0 e2); invertClear H; [invertClear H0; [
  rewrite H, H1; left; reflexivity | right; unfold not; intros;
  apply H; invertClear H0; reflexivity] | right; unfold not;
  intros; apply H1; inversion H; reflexivity]];
  try solve [right; unfold not; intros; inversion H]; try solve
  [addHyp (IHx1 x2); invertClear H; [rewrite H0;
  left; f_equal | right; unfold not; intros; apply H0;
  inversion H; reflexivity]]. addHyp (eqDecExp e e2);
  addHyp (eqDecExp e0 e3); addHyp (eqDecExp e1 e4).
  invertClear H. invertClear H0. invertClear H1. subst.
  left. reflexivity. right. unfold not. intros. apply H0.
  invertClear H1. reflexivity. right. unfold not. intros.
  apply H. invertClear H0. reflexivity. right. unfold not.
  intros. apply H2. invertClear H. reflexivity. Qed.

(**This essentially lifts the substitution function for the expression language up
to the boolean expression language.*)
Fixpoint subBoolExp (s : Subst) (b : BoolExp) : BoolExp :=
  match b with
  | bSufficient e1 e2 => bSufficient (subExp s e1) (subExp s e2)
  | bNot b => bNot (subBoolExp s b)
  | bEqual e1 e2 => bEqual (subExp s e1) (subExp s e2)
  | bPossInc e1 e2 e3 => bPossInc (subExp s e1) (subExp s e2) (subExp s e3)
  end.

(**Evaluation relation on boolean expressions. A boolean expression may evaluate
to a boolean value.*)
Inductive evalBoolExp : BoolExp -> bool -> Prop :=
  | bevalSufficient : forall (e1 e2 : Exp) (m : Mode) (r : Distance),
    evalExp e1 m -> evalExp e2 r ->
    evalBoolExp (bSufficient e1 e2) (suffBool m r)
  | bevalNot : forall (e : BoolExp) (b : bool),
    evalBoolExp e b -> evalBoolExp (bNot e) (negb b)
  | bevalEqualTrue : forall (e1 e2 : Exp) (b : BaseType),
    evalExp e1 b -> evalExp e2 b -> evalBoolExp (bEqual e1 e2) true
  | bevalEqualFalse : forall (e1 e2 : Exp) (b1 b2 : BaseType),
    evalExp e1 b1 -> evalExp e2 b2 -> (b1 <> b2) -> evalBoolExp (bEqual e1 e2) false
  | bevalPossInc : forall (e1 e2 e3 : Exp) (m1 m2 : Mode) (d : Distance),
    evalExp e1 m1 -> evalExp e2 m2 -> evalExp e3 d ->
    evalBoolExp (bPossInc e1 e2 e3) (possIncBool m1 m2 d).

(** A functional definition of the evaluation on boolean expressions.*)
Fixpoint evalBoolExpFun (b : BoolExp) : option bool :=
  match b with 
  | bSufficient e1 e2 =>
    match (evalExpFun e1), (evalExpFun e2) with
    | Some (baseMode m), Some (baseDistance r) => Some (suffBool m r)
    | _, _ => None
    end
  | bNot b => option_map negb (evalBoolExpFun b)
  | bEqual e1 e2 =>
    match (evalExpFun e1), (evalExpFun e2) with
    | Some b1, Some b2 =>
      match eqDecBase b1 b2 with
      | left _ => Some true
      | right _ => Some false
      end
    | _, _ => None
    end
  | bPossInc e1 e2 e3 =>
    match (evalExpFun e1), (evalExpFun e2), (evalExpFun e3) with
    | Some (baseMode m1), Some (baseMode m2), Some (baseDistance d)
      => Some (possIncBool m1 m2 d)
    | _, _, _ => None
    end
  end.

(** A total function for evaluating boolean expressions, which is identical to the
function evalBoolExpFun on well formed inputs, but differs in that it maps ill formed
inputs to false instead of None. This function will be used in the semantics since a
total *)
Definition evalBoolExpFunTot (e : BoolExp) : bool :=
  match evalBoolExpFun e with
  | Some b => b
  | None => false
  end.

(** Sub-Languages syntax notations*)
Notation "E1 (-) E2" := (eSubtract E1 E2) (at level 30).
Notation "E1 (+) E2" := (eAdd E1 E2) (at level 30).
Notation "E1 (.) E2" := (eMult E1 E2) (at level 29).
Notation "e1 =b= e2" := (bEqual e1 e2) (at level 20). 
Notation "| e1 , e2 |" := (eDist e1 e2) (at level 30).
Notation "!~ b" := (bNot b) (at level 25).

(** The evaluation relation on expressions is a partial function i.e.
every expression evaluates to at most one value.*)
Theorem evalExpUnique : forall (e : Exp) (b1 b2 : BaseType),
  evalExp e b1 -> evalExp e b2 -> b1 = b2. intros.
  apply evalExpRelFun in H. apply evalExpRelFun in H0.
  rewrite H in H0. inversion H0. reflexivity. Qed.

(**The boolean expression relation is sound with respect to the function.*)
Theorem evalBoolExpRelFun : forall (e : BoolExp) (b : bool),
  evalBoolExp e b -> evalBoolExpFun e = Some b. intros.
  induction H. apply evalExpRelFun in H. apply evalExpRelFun in H0.
  simpl. rewrite H, H0. reflexivity. simpl. rewrite IHevalBoolExp.
  simpl. reflexivity. apply evalExpRelFun in H. apply evalExpRelFun in H0.
  simpl. rewrite H, H0. addHyp (eqDecBase b b). destruct s. reflexivity.
  apply False_ind. apply n. reflexivity. simpl.
  apply evalExpRelFun in H. apply evalExpRelFun in H0.
  simpl. rewrite H, H0. destruct (eqDecBase b1 b2). apply False_ind.
  apply H1. assumption. reflexivity. apply evalExpRelFun in H1.
  apply evalExpRelFun in H. apply evalExpRelFun in H0. simpl.
  rewrite H, H0, H1. reflexivity. Qed.

From Stdlib Require Import Bool.

(**The boolean expression function is sound with respect to the relation.*)
Theorem evalBoolExpFunRel : forall (e : BoolExp) (b : bool),
  evalBoolExpFun e = Some b -> evalBoolExp e b. induction e; intros.
  (** bSufficient case*)
  simpl in H. remember (evalExpFun e) as v1. remember (evalExpFun e0) as v2.
  destruct v1, v2. destruct b0, b1; inversion H. symmetry in Heqv1, Heqv2.
  apply evalExpFunRel in Heqv1. apply evalExpFunRel in Heqv2.
  constructor; assumption. destruct b0; inversion H. inversion H. inversion H.
  (** bNot case*)
  rewrite negb_involutive_reverse. constructor. apply IHe. inversion H.
  remember (evalBoolExpFun e) as v. destruct v. simpl in H1.
  inversion H1. rewrite H2. symmetry in H2. apply negb_sym in H2.
  rewrite H2. reflexivity. inversion H1.
  (** Equality case*)
  simpl in H. remember (evalExpFun e) as v1. remember (evalExpFun e0) as v2.
  symmetry in Heqv1, Heqv2. destruct v1, v2. addHyp (eqDecBase b0 b1).
  apply evalExpFunRel in Heqv1. apply evalExpFunRel in Heqv2.
  inversion H0; destruct (eqDecBase b0 b1); inversion H. rewrite H1 in Heqv1.
  eapply bevalEqualTrue. apply Heqv1. assumption.
  apply False_ind. apply n. assumption. apply False_ind. apply H1.
  assumption. eapply bevalEqualFalse. apply Heqv1. apply Heqv2.
  assumption. inversion H. inversion H. inversion H.
  (** bPossInc case*)
  simpl in H. remember (evalExpFun e) as v1. remember (evalExpFun e0) as v2.
  remember (evalExpFun e1) as v3. destruct v1, v2, v3.
  destruct b0, b1, b2; inversion H. symmetry in Heqv1, Heqv2, Heqv3.
  apply evalExpFunRel in Heqv1. apply evalExpFunRel in Heqv2.
  apply evalExpFunRel in Heqv3. constructor; assumption.
  destruct b0, b1; inversion H. destruct b0; inversion H.
  destruct b0; inversion H. inversion H. inversion H. inversion H.
  inversion H. Qed.
  


(** The evaluation relation on boolean expressions is a partial function i.e.
every expression evaluates to at most one boolean.*)
Theorem evalBoolExpUnique : forall (e : BoolExp) (b1 b2 : bool),
  evalBoolExp e b1 -> evalBoolExp e b2 -> b1 = b2. intros.
  apply evalBoolExpRelFun in H. apply evalBoolExpRelFun in H0.
  rewrite H in H0. inversion H0. reflexivity. Qed.

(** If the evaluation of the bool exp function is true, then the total function will
evaluate to true, and vice versa.*)
Theorem evalBoolExpTrueTot : forall (e : BoolExp),
  evalBoolExp e true <-> evalBoolExpFunTot e = true. intros.
  split; intros. apply evalBoolExpRelFun in H. unfold evalBoolExpFunTot.
  rewrite H. reflexivity. unfold evalBoolExpFunTot in H.
  remember (evalBoolExpFun e) as b. destruct b. apply evalBoolExpFunRel.
  rewrite H in Heqb. symmetry. assumption. inversion H. Qed.

(**A discrete action is either an input of values on a channel, an output of
values on a channel or a silent (tau) action.*)
Inductive DiscAct :=
  | inAct : Channel -> list BaseType -> DiscAct
  | outAct : Channel -> list BaseType -> DiscAct
  | tauAct : DiscAct.
Notation "c *?" := (inAct c []) (at level 30).
Notation "c *!" := (outAct c []) (at level 30).
Notation "c ;? v" := (inAct c v) (at level 30).
Notation "c ;! v" := (outAct c v) (at level 30).

(** The complement function converts inputs to outputs and vice versa.*)
Definition complement (a : DiscAct) : DiscAct :=
  match a with
  | c ;? v => c ;! v
  | c ;! v => c ;? v
  | tauAct => tauAct
  end.
Notation "a ^" := (complement a) (at level 25).

(** The complement function cancels itself out.*)
Lemma complementInvol (a : DiscAct) : a^^ = a. destruct a; reflexivity. Qed.

Lemma complementNotTau (a : DiscAct) : a <> tauAct -> a^ <> tauAct.
  unfold not. intros. apply H. destruct a; inversion H0; reflexivity. Qed.

Lemma evalExpRelFunEquiv (e : Exp) (b : BaseType) :
  evalExp e b <-> evalExpFun e = Some b. split;
  [apply evalExpRelFun | apply evalExpFunRel]. Qed.

Ltac evalExp_rel_fun_step := match goal with
  [V : _ |_| _ |- _] => apply evalExpRelFun in V end.

Ltac evalExp_rel_fun_tac := repeat evalExp_rel_fun_step.
  
Ltac evalExp_fun_rel_step := match goal with
  [V : Some _ = evalExpFun _ |- _] => symmetry in V;
  apply evalExpFunRel in V end.

Ltac evalExp_fun_rel_tac := repeat evalExp_fun_rel_step.


Lemma evalExp_evalExpFunTime (e : Exp) (t : Time) :
  evalExp e t -> evalExpFunTime e = Some t.
  intros. destruct e; inversion H.
  unfold evalExpFunTime; simpl. destruct t. reflexivity.
  (*Wait time case.*)
  evalExp_rel_fun_tac.
  unfold evalExpFunTime. rewrite H. destruct t. simpl.
  inversion H. rewrite H3, H4 in H6.
  remember (modeTransRelOpt m1 m2). destruct o. simpl in H6.
  f_equal. injection H6. intro. symmetry. assumption.
  inversion H6.
  (*Period case.*)
  evalExp_rel_fun_tac.
  unfold evalExpFunTime. rewrite H. destruct t. simpl.
  repeat f_equal. symmetry. assumption. Qed.

(** A list of expressions evaluates to at most one list of values.*)
Lemma evalExpListsUnique (l : list Exp) (l1 l2 : list BaseType) :
  evalExpLists l l1 -> evalExpLists l l2 -> l1 = l2.
  intro H. revert l2. induction H; intros l3 H3; inversion H3; subst.
  reflexivity. f_equal. eapply evalExpUnique; eassumption.
  apply IHevalExpLists. assumption. Qed.

(** If one list evaluated to another, then the lengths
match.*)
Lemma evalExpListsLength (l : list Exp) : forall (l' : list BaseType),
  evalExpLists l l' -> length l = length l'. induction l; intros.
  inversion H. reflexivity. inversion H. simpl. f_equal.
  apply IHl. assumption. Qed.

(** Evaluation on expressions is decidable.*)
Lemma evalExpDec (e : Exp) (b : BaseType) : decidable (evalExp e b).
  remember (evalExpFun e). destruct o. addHyp (eqDecBase b b0).
  invertClear H. left. apply evalExpFunRel. rewrite H0. symmetry.
  assumption. right. unfold not. intros. apply evalExpRelFun in H.
  rewrite H in Heqo. apply H0. inversion Heqo. reflexivity.
  right. unfold not. intro. apply evalExpRelFun in H. rewrite H in Heqo.
  inversion Heqo. Qed.

(** Evaluation on lists of expressions is decidable.*)
Lemma evalExpListsDec (l : list Exp) (l' : list BaseType) :
  decidable (evalExpLists l l'). generalize dependent l'.
  induction l; intros; destruct l';
  try solve [right; unfold not; intro; inversion H].
  left. constructor. addHyp (evalExpDec a b). invertClear H.
  addHyp (IHl l'). invertClear H. left. constructor; assumption.
  right. unfold not. intro. invertClear H. apply H1. assumption.
  right. unfold not. intro. invertClear H. apply H0. assumption.
  Qed.

(** A functional version of eval exp for lists.*)
Fixpoint evalExpListsFun (l : list Exp) : option (list BaseType) :=
  match l with
  | [] => Some []
  | e :: l => optionMap2 (cons (A := BaseType)) (evalExpFun e) (evalExpListsFun l)
  end.
  
(** The evaluation function on lists implies the relation.*)
Theorem evalExpListsFunRel (l : list Exp) : forall (l' : list BaseType),
  evalExpListsFun l = Some l' -> evalExpLists l l'.
  induction l; intros; inversion H. constructor.
  remember (evalExpFun a). destruct o.
  remember (evalExpListsFun l). destruct o.
  unfold optionMap2 in H1. simpl in H1. inversion H1.
  constructor. apply evalExpFunRel. symmetry. assumption.
  apply IHl. reflexivity. unfold optionMap2 in H1. inversion H1.
  unfold optionMap2 in H1. inversion H1. Qed.
  
(** The evaluation relation on lists implies the function.*)
Theorem evalExpListsRelFun (l : list Exp) : forall (l' : list BaseType),
  evalExpLists l l' -> evalExpListsFun l = Some l'. induction l; intros.
  inversion H. reflexivity. inversion H. simpl. unfold optionMap2.
  unfold option_map. remember (evalExpFun a). destruct o.
  apply IHl in H4. rewrite H4. repeat f_equal. eapply evalExpUnique.
  eapply evalExpFunRel. symmetry. apply Heqo. assumption.
  symmetry in Heqo. apply evalExpRelFun in H2. rewrite H2 in Heqo.
  inversion Heqo. Qed.

(** l either evaluates to something or not.*)
Lemma evalExpListsExDec (l : list Exp) :
  {l' : list BaseType | (evalExpLists l l')} +
  {~exists l', (evalExpLists l l')}.
  remember (evalExpListsFun l). destruct o; [left | right].
  symmetry in Heqo. apply evalExpListsFunRel in Heqo. exists l0.
  assumption. unfold not. intros. invertClear H.
  apply evalExpListsRelFun in H0. rewrite H0 in Heqo. inversion Heqo.
  Qed.

(** If f updated by x onto y is applied to x, then the result is y.*)
Lemma updateAppEq : forall (X : Type) (f : Var -> X) (x : Var) (y : X),
  update f x y x = y. intros. unfold update. unfold varEq.
  remember (varEqDec x x) as e. destruct e. reflexivity.
  apply False_ind. apply n. reflexivity. Qed.

(** If f updated by x to y is applied to z and z is not equal to x, then the
result is (f z).*)
Lemma updateAppNeq : forall (X : Type) (f : Var -> X) (x z : Var) (y : X),
  x <> z -> update f x y z = f z. intros. unfold update. unfold varEq.
  remember (varEqDec x z) as e. destruct e. apply False_ind. apply H.
  assumption. reflexivity. Qed.

(** Lift a variable to a list of variables.*)
Coercion liftVarList (v : Var) : list Var := [v].

(** Lift an expression to a list of expressions.*)
Coercion liftExpList (e : Exp) : list Exp := [e].

(** Makes a typed input explicit: from [H : typedVals xs vs], with xs an explicit list of
variables of known types and vs a variable, replaces vs by one value per variable, each a
constructor of its variable's type applied to a fresh name.*)
Ltac explicit_typed_input := repeat match goal with
  | [H : typedVals (liftVarList _) _ |- _] => unfold liftVarList in H
  | [H : typedVals [] ?vs |- _] => is_var vs; apply typedVals_nil_inv in H; subst vs
  | [H : typedVals (?x :: ?xs) ?vs |- _] => is_var vs;
    let v := fresh "v" in let vs' := fresh "vs" in let E := fresh "E" in
    let T := fresh "T" in let H' := fresh "H" in
    destruct (typedVals_cons_inv _ _ _ H) as [v [vs' [E [T H']]]]; clear H; subst vs;
    destruct v; try discriminate T; clear T
  end.

(** Solves [typedVals xs vs] for explicit lists of variables and values.*)
Ltac typed_vals := solve [unfold typedVals; try unfold liftVarList;
  repeat (constructor; [reflexivity | ]); constructor].


(**Lift a time to an exp.*)
Coercion liftTimeExp (t : Time) : Exp := eBase (baseTime t).

(** Lift a list of variables to a list of expressions.*)
Definition liftListVarExp (l : list Var) : list Exp :=
  map eVar l.

From Stdlib Require Import Logic.FunctionalExtensionality.

(** The substitution of l -> liftListVarExp l is equal to the identity substitution.*)
Lemma listSubRefl : forall (l : list Var),
  listsToSub l (liftListVarExp l) = idSubst. induction l;
  apply functional_extensionality; intros. reflexivity.
  addHyp (eqDecVar a x). invertClear H. rewrite H0.
  simpl. rewrite updateAppEq. reflexivity. simpl.
  rewrite updateAppNeq. rewrite IHl. reflexivity.
  assumption. Qed.
  

(**Every list substitution has a "normal" form. That is, if we have a substitution
x -> l, then there is some l' which is the same length as x such that the substitution
x -> l' is equal to x -> l (according to functional extensionality).*)
Theorem listSubNormal : forall (x : list Var) (l : list Exp),
  {l' : list Exp | length l' = length x /\
  listsToSub x l = listsToSub x l'}. induction x; intros.
  exists (@nil Exp). destruct l; split; reflexivity. destruct l.
  (** In the case where target list is empty, the equivalent substitution is just
   the source list.*)
  exists (liftListVarExp (a :: x)). split. apply map_length.
  rewrite (listSubRefl). reflexivity.
  (** In the case where the target list is not empty, we can proceed by induction.*)
  addHyp (IHx l). clear IHx. invertClear X. invertClear H. rename x0 into l'.
  exists (e :: l'). split. simpl. f_equal. assumption. simpl.
  rewrite H1. reflexivity. Qed.

Lemma idSubExp : forall (e : Exp),
  subExp idSubst e = e. intros. induction e;
  simpl; try rewrite IHe1; try rewrite IHe2; try reflexivity.
  rewrite IHe. reflexivity. rewrite IHe. reflexivity. Qed.

(**The identity substitution leaves lists unchanged.*)
Lemma idSubList : forall (l : list Exp),
  listSub idSubst l = l. intros. induction l. reflexivity.
  simpl. rewrite IHl. rewrite (idSubExp a). reflexivity. Qed.

Lemma idSubBoolExp : forall (b : BoolExp),
  subBoolExp idSubst b = b. induction b.
  simpl. rewrite (idSubExp e0). rewrite (idSubExp e).
  reflexivity. simpl. rewrite IHb. reflexivity.
  simpl. rewrite (idSubExp e0). rewrite (idSubExp e).
  reflexivity. simpl. rewrite (idSubExp e0).
  rewrite (idSubExp e1). rewrite (idSubExp e). reflexivity.
  Qed. 

Lemma resetPreservesId : forall (l : list Var),
  resetSub idSubst l = idSubst. intros. extensionality x.
  unfold resetSub. unfold idSubst. destruct (inVarList x); reflexivity.
  Qed.

Notation "( a , b )" := (pair a b).






































(*********** BEGIN: Matching stuff.*************)


Definition splitSrc {A B : Type} (l : list (A * B)) : list A :=
  fst (split l).

Definition splitTgt {A B : Type} (l : list (A * B)) : list B :=
  snd (split l).

Definition bindListToSub (l : list (Var * Exp)) : Subst :=
  listsToSub (splitSrc l) (splitTgt l).

(** A characterisation of the application of a substitution based on
a bindings list to a variable, which bypasses the conversion to a substitution.*)
Fixpoint bindApp (l : list (Var * Exp)) (x : Var) : Exp :=
  match l with
  | (y, e) :: l' => if eqDecVar x y then e else bindApp l' x
  | _ => eVar x
  end.

Lemma bindListToSubCons (x : Var) (e : Exp) (l : list (Var * Exp)) :
  bindListToSub ((x, e) :: l) = update (bindListToSub l) x e.
  unfold bindListToSub. unfold splitSrc. unfold splitTgt. simpl.
  destruct (split l). simpl. reflexivity. Qed.

(** Proof that the bindApp function is correct w.r.t. the substitution conversion.*)
Theorem bindApp_subst (l : list (Var * Exp)) (x : Var) :
  bindApp l x = (bindListToSub l) x. induction l. unfold bindListToSub.
  simpl. reflexivity. destruct a. rewrite bindListToSubCons. simpl.
  remember (eqDecVar x v). destruct s. rewrite e0. rewrite updateAppEq.
  reflexivity. rewrite updateAppNeq. assumption. unfold not. intro. apply n.
  symmetry. assumption. Qed.



(** (x, e) is the first occurrence of a map of x in l if there is no
(x, e') preceding it in the list.*)
Inductive firstOcc (x : Var) (e : Exp) : list (Var * Exp) -> Prop :=
  | fstocHd (l : list (Var * Exp)) : firstOcc x e ((x, e) :: l)
  | fstocTl (y : Var) (e' : Exp) (l : list (Var * Exp)) :
    firstOcc x e l -> x <> y -> firstOcc x e ((y, e') :: l).

Lemma firstOcc_unique (x : Var) (e e' : Exp) (l : list (Var * Exp)) :
  firstOcc x e l -> firstOcc x e' l -> e = e'. intros.
  induction H; inversion H0. reflexivity. apply False_ind.
  apply H4. reflexivity. apply False_ind. apply H1. assumption.
  apply IHfirstOcc. assumption. Qed.

Lemma splitSrcCons (x : list (Var*Exp)) (a : Var) (e : Exp):
  splitSrc ((a, e) :: x) = a :: (splitSrc x). unfold splitSrc.
  simpl. destruct (split x). simpl. reflexivity. Qed.

Lemma firstOcc_splitSrc (x : Var) (e : Exp) (l : list (Var * Exp)) :
  firstOcc x e l -> x _: splitSrc l. intros. induction H.
  rewrite splitSrcCons. left. reflexivity. rewrite splitSrcCons.
  right. assumption. Qed.

Lemma splitSrc_firstOcc_ex (x : Var) (l : list (Var * Exp)) :
  x _: splitSrc l -> exists e, firstOcc x e l. induction l; intros.
  inversion H. destruct a. rewrite splitSrcCons in H.
  addHyp (eqDecVar x v). invertClear H0. exists e. rewrite H1.
  constructor. elim H; intro. apply False_ind. apply H1. symmetry.
  assumption. addHyp (IHl H0). invertClear H2.
  exists x0. constructor;assumption. Qed.

(** A preorder on binding lists that puts one list before the other if the latter
agrees with the former on all variables in the source of the former.*)
Definition preordBindList (l1 l2 : list (Var * Exp)) : Prop :=
  forall (x : Var) (e : Exp), firstOcc x e l1 -> firstOcc x e l2.
Notation "l1 <[] l2" := (preordBindList l1 l2) (at level 70).

(**The empty list is the bottom element of the lattice.*)
Lemma preord_emp (l : list (Var * Exp)) :
  [] <[] l. unfold preordBindList. intros.
  inversion H. Qed.

(** The preorder that has been defined is reflexive.*)
Lemma preordBindList_refl (l : list (Var * Exp)) : l <[] l.
  induction l; unfold preordBindList; intros; assumption. Qed.

(*TOGO: COMH BASICS*)
Lemma incl_hd_eq {A : Type} (l1 l2 : list A) (x : A) :
  incl l1 l2 -> incl (x :: l1) (x :: l2). unfold incl. intros.
  inversion H0. rewrite H1. constructor. reflexivity.
  apply in_cons. apply H. apply H1. Qed.

(** If one binding list is less than another according to the preorder,
then the source of the former is contained in the source of the latter
according to incl.*)
Lemma pre_incl_splitSrc (l1 l2 : list (Var * Exp)) :
  l1 <[] l2 -> incl (splitSrc l1) (splitSrc l2). intro.
  unfold incl. intros. apply splitSrc_firstOcc_ex in H0.
  invertClear H0. apply H in H1. eapply firstOcc_splitSrc.
  apply H1. Qed.

(** The preorder that has been defined is transitive.*)
Lemma preordBindList_trans (l1 l2 l3: list (Var * Exp)) :
  l1 <[] l2 -> l2 <[] l3 -> l1 <[] l3.
  unfold preordBindList. intros. apply H0. apply H. assumption. Qed.

(** Gives back a list whose elements are those of l minus the ones containing a
variable from l'.*)
Fixpoint excludeSrc (l : list (Var * Exp)) (l' : list Var) : list (Var * Exp) :=
  match l with
  | [] => []
  | (x, e) :: ls => if (in_dec eqDecVar x l') then excludeSrc ls l'
    else (x, e) :: excludeSrc ls l'
  end.

(** The source of l with l' excluded is included within the source of l.*)
Lemma excludeSrc_incl (l : list (Var * Exp)) (l' : list Var) : 
  incl (splitSrc (excludeSrc l l')) (splitSrc l). induction l.
  simpl. apply incl_refl. simpl. destruct a. remember (in_dec eqDecVar v l').
  destruct s. rewrite splitSrcCons. apply incl_tl. assumption.
  rewrite splitSrcCons. apply incl_cons. rewrite splitSrcCons. constructor.
  reflexivity. rewrite splitSrcCons. apply incl_tl. assumption. Qed.

Lemma set_inter_nil {A : Type} (l : list A)
  (p : forall (x y : A), {x = y} + {x <> y}) : set_inter p l [] = [].
  induction l. reflexivity. simpl. assumption. Qed. 

(**If we exclude l' from l, then the source of the resultant list has no elements in
common with l'.*)
Lemma excludeSrc_inter_emp (l : list (Var * Exp)) (l' : list Var) : 
  set_inter eqDecVar (splitSrc (excludeSrc l l')) l' = []. induction l.
  reflexivity. unfold excludeSrc. destruct a. remember (in_dec eqDecVar v l').
  destruct s. apply IHl. rewrite splitSrcCons. unfold set_inter.
  addHyp (set_mem_complete2 eqDecVar v l' n). rewrite H.
  apply IHl. Qed.

Lemma exclude_nil (l : list (Var * Exp)) : 
  excludeSrc l [] = l. induction l. reflexivity.
  simpl. rewrite IHl. destruct a. reflexivity. Qed.

Lemma exclude_in_splitSrc (v : Var) (x : list Var) (l : list (Var * Exp)) :
  v _: x -> ~v _: splitSrc (excludeSrc l x). intros. induction l.
  unfold not. intros. inversion H0. unfold not. intros.
  destruct a. simpl in H0. remember (in_dec eqDecVar v0 x).
  destruct s. apply IHl. assumption. rewrite splitSrcCons in H0.
  inversion H0. apply n. rewrite H1. assumption. apply IHl.
  assumption. Qed.

Lemma pre_notIn_cons (x : Var) (e : Exp) (l l' : list (Var * Exp)) :
  ~x _: splitSrc l -> l <[] l' -> l <[] ((x, e) :: l'). unfold preordBindList.
  intros. addHyp H1. rename H2 into Q. apply H0 in H1. constructor. assumption.
  unfold not. intros. apply H. rewrite <- H2. eapply firstOcc_splitSrc. apply Q.
  Qed.

Lemma exclude_preord (l' : list Var) (l : list (Var * Exp)) :
  (excludeSrc l l') <[] l. unfold preordBindList. intros.
  generalize dependent l'. induction l; intros. inversion H.
  destruct a. simpl in H. remember (in_dec eqDecVar v l').
  destruct s. assert (x <> v). unfold not. intro.
  rewrite H0 in H. apply firstOcc_splitSrc in H.
  eapply exclude_in_splitSrc. apply i. apply H.
  constructor;[|assumption]. eapply IHl. apply H.
  inversion H. constructor. constructor;[|assumption].
  eapply IHl. apply H2. Qed.

Lemma preord_exclude (l1 l2 : list (Var * Exp)) (x : list Var) :
  preordBindList l1 (excludeSrc l2 x) -> preordBindList l1 l2.
  intros. eapply preordBindList_trans. apply H.
  apply exclude_preord. Qed.

Lemma exclude_firstOcc (x : Var) (e : Exp)
  (l1 : list (Var * Exp)) (l2 : list Var) :
  firstOcc x e (excludeSrc l1 l2) -> firstOcc x e l1.
  intros. assert (~x _: l2). unfold not. intros.
  apply firstOcc_splitSrc in H. eapply exclude_in_splitSrc.
  apply H0. apply H. induction l1. inversion H. destruct a. simpl in H.
  addHyp (eqDecVar x v). invertClear H1.
  remember (in_dec eqDecVar v l2). destruct s. apply False_ind.
  apply H0. rewrite H2. assumption. rewrite H2 in H.
  inversion H. rewrite H2. constructor. apply False_ind.
  apply H6. reflexivity. constructor;[|assumption].
  apply IHl1. remember (in_dec eqDecVar v l2).
  destruct s. assumption. inversion H.
  apply False_ind. apply H2. assumption.
  assumption. Qed.
 
Lemma firstOcc_notIn_exclude (x : Var) (e : Exp)
  (l1 : list (Var * Exp)) (l2 : list Var) :
  firstOcc x e l1 -> ~x _: l2 -> firstOcc x e (excludeSrc l1 l2).
  intros. induction l1. inversion H. simpl. destruct a.
  remember (in_dec eqDecVar v l2). destruct s. apply IHl1.
  inversion H. apply False_ind. apply H0. rewrite H2.
  assumption. assumption. addHyp (eqDecVar x v).
  invertClear H1. rewrite H2 in H. invertClear H.
  rewrite H2. constructor. apply False_ind. apply H6.
  reflexivity. constructor. apply IHl1. invertClear H.
  apply False_ind. apply H2. assumption. assumption.
  assumption. Qed.

Lemma preord_cons_excl (v : Var) (e : Exp) (l1 l2 : list (Var * Exp)) :
  l1 <[] ((v, e) :: l2) -> (excludeSrc l1 [v]) <[] l2.
  unfold preordBindList. intros. assert (~x _: [v]).
  apply firstOcc_splitSrc in H0. unfold not. intro.
  eapply exclude_in_splitSrc. apply H1. apply H0.
  apply exclude_firstOcc in H0.
  apply H in H0. inversion H0. rewrite H3 in H1.
  apply False_ind. apply H1. left. reflexivity.
  assumption. Qed.

(** If (v, e) is the first occurrence of v in l1, then the question of whether l1
is less than l2 by the preorder is the same as the question as to whether l1 with
v excluded is less than l2.*)
Lemma fst_pre_cons_excl (v : Var) (e : Exp) (l1 l2 : list (Var * Exp)) :
  firstOcc v e l1 -> (l1 <[] ((v, e) :: l2) <->
  excludeSrc l1 v <[] l2). intros. split. apply preord_cons_excl.
  unfold preordBindList. intros. addHyp (in_dec eqDecVar x [v]).
  invertClear H2. invertClear H3;[|inversion H2].
  rewrite H2 in H. replace e0 with e. rewrite H2. constructor.
  eapply firstOcc_unique. apply H. assumption. constructor.
  apply H0. eapply firstOcc_notIn_exclude; assumption.
  unfold not. intro. apply H3. rewrite H2. left. reflexivity. Qed. 

Lemma in_src_ex_firstOcc (v : Var) (l : list (Var * Exp)) :
  v _: splitSrc l -> exists e, firstOcc v e l. intros.
  induction l. inversion H. destruct a. rewrite splitSrcCons in H.
  addHyp (eqDecVar v v0). invertClear H0. rewrite H1. exists e.
  constructor. elim H; intros. apply False_ind. apply H1.
  rewrite H0. reflexivity. apply IHl in H0. invertClear H0.
  exists x. constructor; assumption. Qed.

Lemma notIn_src_cons_eq (v : Var) (e : Exp) (l1 l2 : list (Var * Exp)) :
  ~ v _: (splitSrc l1) -> (l1<[](v, e) :: l2 <-> l1 <[] l2).
  intros. split; unfold preordBindList; intros.
  addHyp H1. apply H0 in H1. invertClear H1. apply firstOcc_splitSrc in H2.
  apply False_ind. apply H. rewrite <- H4. assumption. assumption.
  constructor. apply H0. assumption. unfold not. intro.
  apply H. rewrite <- H2. eapply firstOcc_splitSrc. apply H1. Qed.

Theorem dec_preordBindList (l1 l2 : list (Var * Exp)) :
  decidable (l1 <[] l2). generalize dependent l1. 
  induction l2; intros. destruct l1. left. apply preord_emp.
  right. unfold not. intros. destruct p.
  assert (firstOcc v e []). apply H. constructor. inversion H0.
  destruct a. addHyp (in_dec eqDecVar v (splitSrc l1)).
  invertClear H. apply in_src_ex_firstOcc in H0.
  invertClear H0. rename x into e'. addHyp (eqDecExp e e').
  invertClear H0. rewrite <- H1 in H. clear H1.
  unfold decidable. rewrite fst_pre_cons_excl;[|assumption].
  apply IHl2. right. unfold not. unfold preordBindList.
  intros. apply H0 in H. inversion H. apply H1.
  rewrite H3. reflexivity. apply H6. reflexivity.
  unfold decidable. rewrite notIn_src_cons_eq;[|assumption].
  apply IHl2. Qed.
  
(**Builds the identity bindings list for a given source list x.*)
Fixpoint idBindList (x : list Var) : list (Var * Exp) :=
  match x with
  | [] => []
  | a :: xs => (a, eVar a) :: idBindList xs
  end.

(**The identity bind list as created by the said function gives
rise to the identity substitution.*)
Lemma idBindList_idSub (x : list Var) :
  bindListToSub (idBindList x) = idSubst. apply functional_extensionality.
  intros. remember (idBindList x) as l. generalize dependent l.
  induction x; intros. unfold bindListToSub.
  simpl. simpl in Heql. rewrite Heql. reflexivity.
  destruct l; inversion Heql. addHyp (IHx l H1). clear IHx.
  simpl. rewrite bindListToSubCons. addHyp (eqDecVar a x0).
  invertClear H2. rewrite H3. rewrite updateAppEq. unfold idSubst.
  reflexivity. rewrite updateAppNeq;[|assumption]. rewrite <- H1.
  assumption. Qed.

(** The source of the identity bindings list built from x is itself x.*)
Lemma srcIdBindList (x : list Var) : splitSrc (idBindList x) = x.
  induction x. reflexivity. simpl. rewrite splitSrcCons. f_equal.
  assumption. Qed.

Lemma preord_emp_eq (l : list (Var * Exp)) : 
  l<[][] -> l = []. unfold preordBindList. intros.
  destruct l. reflexivity. destruct p.
  cut (firstOcc v e []). intros. inversion H0.
  apply H. constructor. Qed.

Lemma bindApp_cons_eq (x : Var) (e : Exp) (l : list (Var * Exp)) :
  bindApp ((x, e) :: l) x = e. unfold bindApp. remember (eqDecVar x x).
  destruct s. reflexivity. apply False_ind. apply n. reflexivity. Qed.

Lemma bindApp_cons_neq (x y : Var) (e : Exp) (l : list (Var * Exp)) :
  x <> y -> bindApp ((x, e) :: l) y = bindApp l y. intros.
  unfold bindApp. remember (eqDecVar y x).
  destruct s. apply False_ind. apply H. rewrite e0. reflexivity.
  reflexivity. Qed.

Lemma firstOcc_bindApp (x : Var) (e : Exp) (l : list (Var * Exp)) :
  firstOcc x e l -> bindApp l x = e. intros. induction H.
  apply bindApp_cons_eq. rewrite <- IHfirstOcc. apply bindApp_cons_neq.
  unfold not. intros. apply H0. rewrite H1. reflexivity. Qed.

Lemma firstOcc_cons_eq (x : Var) (e e' : Exp) (l : list (Var * Exp)) : 
  firstOcc x e' ((x, e) :: l) -> e = e'. intros. inversion H.
  reflexivity. apply False_ind. apply H4. reflexivity. Qed.

Lemma excl_cons (x : Var) (e : Exp) (l1 : list (Var * Exp)) (l2 : list Var) :
  ~x _: l2 -> excludeSrc ((x, e) :: l1) l2 = (x, e) :: excludeSrc l1 l2.
  intros. simpl. remember (in_dec eqDecVar x l2). destruct s.
  apply False_ind. apply H. assumption. reflexivity. Qed.

Lemma notIn_bindApp_excl (x : Var) (l1 : list (Var * Exp)) (l2 : list Var) :
  ~x _: l2 -> bindApp l1 x = bindApp (excludeSrc l1 l2) x. intros.
  induction l1. reflexivity. destruct a. addHyp (eqDecVar v x).
  invertClear H0. rewrite H1. rewrite excl_cons.
  repeat rewrite bindApp_cons_eq. reflexivity. assumption.
  simpl. remember (eqDecVar x v). destruct s.
  apply False_ind. apply H1. symmetry. assumption.
  remember (in_dec eqDecVar v l2). destruct s.
  rewrite IHl1. reflexivity. rewrite bindApp_cons_neq.
  rewrite IHl1. reflexivity. assumption. Qed.

Lemma in_splitSrc_excl (x : Var) (l1 : list (Var * Exp)) (l2 : list Var) :
  ~x _: l2 -> x _: splitSrc l1 -> x _: splitSrc (excludeSrc l1 l2). intros.
  induction l1. inversion H0. destruct a. simpl. remember (in_dec eqDecVar v l2).
  destruct s. apply IHl1. rewrite splitSrcCons in H0. inversion H0.
  apply False_ind. apply H. rewrite <- H1. assumption. apply H1.
  rewrite splitSrcCons. rewrite splitSrcCons in H0. inversion H0.
  rewrite H1. constructor. reflexivity. right. apply IHl1.
  apply H1. Qed.

(** If l1 <[] l2 then the substitutions generated by l1 and l2 are equivalent
for all variables in the source of l1.*)
Theorem preord_subst (l1 l2 : list (Var * Exp)) (x : Var) :
  l1 <[] l2 -> x _: splitSrc l1 -> (bindListToSub l1) x = (bindListToSub l2) x.
  intros. repeat rewrite <- bindApp_subst.
  generalize dependent l1. induction l2; intros. apply preord_emp_eq in H.
  rewrite H. reflexivity. destruct a. addHyp (eqDecVar v x). invertClear H1.
  rewrite H2. rewrite H2 in H. rewrite bindApp_cons_eq.
  apply firstOcc_bindApp. apply in_src_ex_firstOcc in H0. invertClear H0.
  addHyp H1. apply H in H1. apply firstOcc_cons_eq in H1. rewrite H1.
  assumption. rewrite bindApp_cons_neq;[|assumption].
  apply preord_cons_excl in H. rewrite (notIn_bindApp_excl x l1 v).
  apply IHl2. assumption. apply in_splitSrc_excl. unfold not.
  intros. apply H2. inversion H1. assumption. inversion H3.
  assumption. unfold not. intros. apply H2. inversion H1.
  assumption. inversion H3. Qed.

(** Takes the binding list l and restricts its source to x, preserving any
bindings of l based in x and acting as the identity otherwise.*)
Fixpoint restrictSrc (l : list (Var * Exp)) (x : list Var) :
  list (Var * Exp) :=
  match x with
  | [] => []
  | a :: xs => (a, ((bindListToSub l) a)) :: (restrictSrc l xs)
  end.

(** The source of the restrict source function is actually correct.*)
Lemma restrictSrc_source (l : list (Var * Exp)) (x : list Var) :
  splitSrc (restrictSrc l x) = x. induction x. unfold splitSrc.
  simpl. reflexivity. simpl. rewrite splitSrcCons. f_equal.
  assumption. Qed.
    
Lemma restrictSrc_in (y : Var) (x : list Var) (l : list (Var * Exp)) :
  y _: x -> (bindListToSub (restrictSrc l x)) y = (bindListToSub l) y.
  intro. induction x; inversion H. rewrite <- H0. simpl.
  rewrite bindListToSubCons. rewrite updateAppEq. reflexivity.
  apply IHx in H0. clear IHx. simpl. rewrite bindListToSubCons.
  addHyp (eqDecVar a y). invertClear H1. rewrite H2.
  rewrite updateAppEq. reflexivity. rewrite updateAppNeq;assumption.
  Qed.

Lemma listSub_notIn (x : Var) (l : list Var) (l' : list Exp) :
  ~x _: l -> (listsToSub l l') x = (eVar x). intros.
  generalize dependent l'. induction l; intros.
  simpl. destruct l'; reflexivity. destruct l'. reflexivity.
  simpl. rewrite updateAppNeq. apply IHl. unfold not. intro.
  apply H. apply in_cons. assumption. unfold not. intro.
  apply H. rewrite H0. constructor. reflexivity. Qed.

(** If the source of l is included in x, then restricting l to x will yield a binding list
whose corresponding substitution is the same as that of l.*)
Lemma restrictSrc_incl_subEq (l : list (Var * Exp)) (x : list Var) :
  incl (splitSrc l) x -> bindListToSub (restrictSrc l x) = bindListToSub l.
  intros. apply functional_extensionality. intros.
  addHyp (in_dec eqDecVar x0 x). invertClear H0.
  rewrite restrictSrc_in;[reflexivity|assumption].
  unfold bindListToSub. rewrite listSub_notIn. rewrite listSub_notIn.
  reflexivity. unfold not. intros. apply H1. apply H. assumption.
  unfold not. rewrite restrictSrc_source. intro. apply H1. assumption. Qed.

Lemma inVarList_in (x : Var) (l : list Var) :
  inVarList x l = true <-> x _: l. split; intros.
  induction l. inversion H. inversion H.
  remember (varEq x a). destruct b. constructor.
  unfold varEq in Heqb. remember (varEqDec x a).
  destruct s. symmetry. assumption. inversion Heqb.
  apply IHl in H1. apply in_cons. assumption.
  induction l. inversion H. inversion H.
  rewrite H0. simpl. remember (varEq x x).
  destruct b. reflexivity. unfold varEq in Heqb.
  remember (varEqDec x x). destruct s. inversion Heqb.
  apply False_ind. apply n. reflexivity. 
  apply IHl in H0. simpl. remember (varEq x a).
  destruct b. reflexivity. assumption. Qed.

Lemma preord_inter_exclude (l l' : list (Var * Exp)) (x : list Var) :
  set_inter eqDecVar (splitSrc l) x = [] -> preordBindList l l' ->
  preordBindList l (excludeSrc l' x). 
  unfold preordBindList. intros. apply firstOcc_notIn_exclude.
  apply H0. assumption. unfold not. intros.
  apply firstOcc_splitSrc in H1. eapply set_inter_nil_in1.
  apply H. apply H1. assumption. Qed.

Definition joinBindList (l l1 l2 : list (Var * Exp)) : Prop :=
  preordBindList l1 l /\ preordBindList l2 l.

Lemma joinBindList_symm (l l1 l2 : list (Var * Exp)) :
  joinBindList l l1 l2 -> joinBindList l l2 l1. intros.
  inversion H. split; assumption. Qed.

Lemma dec_joinBindList (l l1 l2 : list (Var * Exp)) :
  decidable (joinBindList l l1 l2).
  addHyp (dec_preordBindList l1 l). addHyp (dec_preordBindList l2 l).
  invertClear H. invertClear H0. left. split; assumption.
  right. unfold not. intro. invertClear H0. apply H. assumption.
  right. unfold not. intro. invertClear H. apply H1. assumption.
  Qed.

(** Normalise the list l, by removing all redundant pairs (x, e) that are
preceded in the list, and thus overwritten, by (x, e').*)
Fixpoint normBindList (l : list (Var * Exp)) : list (Var * Exp) :=
  match l with
  | [] => []
  | (x, e) :: l' => (x, e) :: excludeSrc (normBindList l') [x]
  end.

Lemma src_norm_in_equiv (x : Var) (l : list (Var * Exp)) :
  x _: splitSrc (normBindList l) <-> x _: splitSrc l. induction l.
  reflexivity. simpl. destruct a. repeat rewrite splitSrcCons.
  addHyp (eqDecVar x v). invertClear H. rewrite H0.
  simpl. split; intro Q; invertClear Q; left; reflexivity.
  split; intros; (elim H; intro; [apply False_ind;
  apply H0; symmetry; assumption |]). right.
  rewrite <- IHl. apply excludeSrc_incl in H1. assumption.
  right. apply in_splitSrc_excl. unfold not. intros.
  apply H0. inversion H2. symmetry. assumption. inversion H3.
  rewrite IHl. assumption. Qed.

Lemma norm_sub_equiv (l : list (Var * Exp)) :
  bindListToSub l = bindListToSub (normBindList l).
  apply functional_extensionality. intros.
  repeat rewrite <- bindApp_subst. induction l; simpl.
  reflexivity. destruct a. remember (eqDecVar x v).
  destruct s. rewrite e0. rewrite bindApp_cons_eq.
  reflexivity. assert (~x _: [v]). unfold not. intro.
  apply n. inversion H. symmetry. assumption. inversion H0.
  rewrite bindApp_cons_neq;[|unfold not; intro; apply n;
  symmetry; assumption].
  rewrite <- notIn_bindApp_excl. apply IHl. assumption.
  Qed.

(**An alternative characterisation of the preorder.*)
Theorem preordBindListAlt (l1 l2 : list (Var * Exp)) :
  l1 <[] l2 <->
  (forall x : Var, x _: (splitSrc l1) -> x _: (splitSrc l2) /\
  (bindListToSub l1) x = (bindListToSub l2) x). split; intros.
  (*Left to right*)
  split. eapply pre_incl_splitSrc. apply H. assumption.
  repeat rewrite <- bindApp_subst. apply in_src_ex_firstOcc in H0.
  invertClear H0. addHyp H1. apply H in H0.
  repeat (rewrite (firstOcc_bindApp x x0);[|assumption]).
  reflexivity.
  (*Right to left*)
  unfold preordBindList. intros. addHyp H0. apply firstOcc_splitSrc in H1.
  apply H in H1. invertClear H1. clear H. apply in_src_ex_firstOcc in H2.
  invertClear H2. rename x0 into e'. addHyp (eqDecExp e e').
  invertClear H1. rewrite H2. assumption. apply False_ind.
  apply H2. repeat rewrite <- bindApp_subst in H3.
  assert (bindApp l1 x = e). apply firstOcc_bindApp. assumption.
  assert (bindApp l2 x = e'). apply firstOcc_bindApp. assumption.
  rewrite <- H1. rewrite <- H4. assumption. Qed.

Lemma preord_norm (l1 : list (Var * Exp)) :
  l1 <[] (normBindList l1) /\ (normBindList l1) <[] l1.
  repeat rewrite preordBindListAlt.
  split; intros;[rewrite src_norm_in_equiv; rewrite <- norm_sub_equiv
  | rewrite <- src_norm_in_equiv; rewrite <- norm_sub_equiv];(split;
  [assumption|reflexivity]). Qed.

(** lubBindList l l1 l2 roughly means that l is a least upper bound
for bind lists l1 and l2.*)
Inductive lubBindList : list (Var * Exp) -> list (Var * Exp) ->
  list (Var * Exp) -> Prop :=
  | lubbl (l1 l2 : list (Var * Exp)) :
    joinBindList (normBindList (excludeSrc l1 (splitSrc l2) ++ l2)) l1 l2 ->
    lubBindList (normBindList (excludeSrc l1 (splitSrc l2) ++ l2)) l1 l2.

Lemma lubPreordFst (l l1 l2 : list (Var * Exp)) :
  lubBindList l l1 l2 -> preordBindList l1 l. intro. inversion H.
  inversion H0. assumption. Qed.

Lemma lubPreordSnd (l l1 l2 : list (Var * Exp)) :
  lubBindList l l1 l2 -> preordBindList l2 l. intro. inversion H.
  inversion H0. assumption. Qed.

Lemma lubBindListUnique (l l' l1 l2 : list (Var * Exp)) :
  lubBindList l l1 l2 -> lubBindList l' l1 l2 ->
  l = l'. intros. inversion H. inversion H0. reflexivity. Qed.

(** The existence of a least upper bound for any pair of binding lists is
a decidable property.*)
Lemma decLubBindList (l1 l2 : list (Var * Exp)) :
  decidable (exists l, lubBindList l l1 l2). 
  addHyp (dec_joinBindList (normBindList (excludeSrc l1 (splitSrc l2) ++ l2)) l1 l2).
  invertClear H. left. exists (normBindList (excludeSrc l1 (splitSrc l2) ++ l2)).
  constructor. assumption. right. unfold not. intros. invertClear H.
  invertClear H1. apply H0. assumption. Qed. 

Lemma notIn_bindList_id (x : Var) (l : list (Var * Exp)) :
  ~x _: (splitSrc l) -> eVar x = bindListToSub l x. intros.
  rewrite <- bindApp_subst. induction l. simpl. reflexivity.
  simpl. destruct a. remember (eqDecVar x v). destruct s.
  apply False_ind. apply H. rewrite e0. rewrite splitSrcCons.
  constructor. reflexivity. apply IHl. unfold not. intros.
  apply H. rewrite splitSrcCons. right. assumption. Qed.

Lemma excludeSrc_in_cons_eq (v : Var) (l1 : list (Var * Exp))
  (l2 : list Var) (e : Exp) :
  v _: l2 -> excludeSrc ((v, e) :: l1) l2 = excludeSrc l1 l2.
  intros. simpl. remember (in_dec eqDecVar v l2). destruct s.
  reflexivity. apply False_ind. apply n. assumption. Qed.

Lemma append_firstOcc (x : Var) (e : Exp) (l1 l2 : list (Var * Exp)) :
  firstOcc x e (l1 ++ l2) -> firstOcc x e l1 \/ firstOcc x e l2.
  intros. induction l1. right. apply H. inversion H. left.
  constructor. apply IHl1 in H2. invertClear H2. left.
  constructor; assumption. right. assumption. Qed.

Lemma firstOcc_append (x : Var) (e : Exp) (l1 l2 : list (Var * Exp)) :
  firstOcc x e l1 -> firstOcc x e (l1 ++ l2). intros. induction H;
  simpl; constructor; try assumption. Qed.

Lemma lubBindList_pre_join (l l1 l2 : list (Var * Exp)) :
  joinBindList l l1 l2 -> (normBindList (excludeSrc l1 (splitSrc l2) ++ l2)) <[] l.
  intros. addHyp (preord_norm (excludeSrc l1 (splitSrc l2) ++ l2)).
  invertClear H0. clear H1. eapply preordBindList_trans;[apply H2 |].
  clear H2. invertClear H. unfold preordBindList. intros.
  apply append_firstOcc in H. invertClear H. apply exclude_firstOcc in H2.
  apply H0. assumption. apply H1. assumption. Qed.

Lemma firstOcc_exclude_append (x : Var) (e : Exp) (l1 l2 : list (Var * Exp)) :
  firstOcc x e l2 ->
  firstOcc x e (excludeSrc l1 (splitSrc l2) ++ l2). intros.
  induction l1. apply H. destruct a. simpl. remember (in_dec eqDecVar v (splitSrc l2)).
  destruct s. assumption. cut (x <> v). intros. constructor;[|assumption].
  apply IHl1. unfold not. intros. apply n. rewrite <- H0.
  eapply firstOcc_splitSrc. apply H. Qed.
  
Lemma join_firstOcc_eq (x : Var) (e e' : Exp) (l l1 l2 : list (Var * Exp)) :
  joinBindList l l1 l2 -> firstOcc x e l1 -> firstOcc x e' l2 ->
  e = e'. intros. invertClear H. apply H2 in H0. apply H3 in H1.
  eapply firstOcc_unique. apply H0. assumption. Qed.

Lemma join_lubBindList_ex (l l1 l2 : list (Var * Exp)) :
  joinBindList l l1 l2 -> exists l',
  lubBindList l' l1 l2 /\ preordBindList l' l. intros.
  exists (normBindList (excludeSrc l1 (splitSrc l2) ++ l2)).
  split;[|apply lubBindList_pre_join;assumption]. constructor.
  addHyp (preord_norm (excludeSrc l1 (splitSrc l2) ++ l2)).
  invertClear H0. clear H2. split;
  (eapply preordBindList_trans;[|apply H1]).
  clear H1. unfold preordBindList. intros.
  addHyp (in_dec eqDecVar x (splitSrc l2)). invertClear H1.
  apply splitSrc_firstOcc_ex in H2. invertClear H2.
  apply firstOcc_exclude_append. rename x0 into e'.
  replace e with e'. assumption. symmetry. eapply join_firstOcc_eq.
  apply H. apply H0. assumption. apply firstOcc_append.
  apply firstOcc_notIn_exclude; assumption.
  clear H1. unfold preordBindList. intros.
  apply firstOcc_exclude_append. assumption. Qed.

(** If a substitution based on a list l is reset on the list of variables x, and none
of these variables of x is in the source of l, then the substitution remains unchanged
after the reset operation.*)
Theorem reset_id (l : list (Var * Exp)) (x : list Var) :
  set_inter eqDecVar (splitSrc l) x = [] ->
  resetSub (bindListToSub l) x = (bindListToSub l). intros.
  apply functional_extensionality. intros. unfold resetSub.
  remember (inVarList x0 x). destruct b. apply notIn_bindList_id.
  eapply set_inter_nil_in2. apply H. rewrite <- inVarList_in.
  symmetry. assumption. reflexivity. Qed.

(**The substitution formed after excluding x from l is the same as
that formed from l with x reset.*)
Lemma exclude_reset (l : list (Var * Exp)) (x : list Var) : 
  bindListToSub (excludeSrc l x) = resetSub (bindListToSub l) x.
  apply functional_extensionality. intros. induction l.
  simpl. rewrite reset_id. reflexivity. reflexivity.
  destruct a. simpl. remember (in_dec eqDecVar v x). destruct s.
  rewrite IHl. unfold resetSub. remember (inVarList x0 x). 
  destruct b. reflexivity. rewrite bindListToSubCons.
  rewrite updateAppNeq. reflexivity. unfold not. intros.
  rewrite <- H in Heqb. clear Heqs. rewrite <- inVarList_in in i.
  rewrite i in Heqb. inversion Heqb. rewrite bindListToSubCons.
  rewrite bindListToSubCons. addHyp (eqDecVar v x0). invertClear H.
  rewrite H0. rewrite updateAppEq. clear Heqs. rewrite H0 in n.
  unfold resetSub. remember (inVarList x0 x). destruct b.
  symmetry in Heqb. rewrite inVarList_in in Heqb. apply False_ind.
  apply n. assumption. rewrite updateAppEq. reflexivity.
  rewrite updateAppNeq;[|assumption]. rewrite IHl.
  unfold resetSub. remember (inVarList x0 x). destruct b.
  reflexivity. rewrite updateAppNeq;[|assumption]. reflexivity. Qed.

(** A characterisation of the matching problem for expressions. This says that
the e1 is equal to the e2 with the substitution l applied.*)
Inductive matchExp : Exp -> Exp -> list (Var * Exp) -> Prop :=
  | meVar (x : Var) (e : Exp) : matchExp e (eVar x) ([(x, e)])
  | meBase (b : BaseType) : matchExp (eBase b) (eBase b) []
  | meSub (l l1 l2 : list (Var * Exp)) (e1 e2 e1' e2' : Exp) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> lubBindList l l1 l2 ->
    matchExp (eSubtract e1 e2) (eSubtract e1' e2') l
  | meAdd (l l1 l2 : list (Var * Exp)) (e1 e2 e1' e2' : Exp) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> lubBindList l l1 l2 ->
    matchExp (eAdd e1 e2) (eAdd e1' e2') l
  | meMult (l l1 l2 : list (Var * Exp)) (e1 e2 e1' e2' : Exp) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> lubBindList l l1 l2 ->
    matchExp (eMult e1 e2) (eMult e1' e2') l
  | meWaitTime (l l1 l2 : list (Var * Exp)) (e1 e2 e1' e2' : Exp) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> lubBindList l l1 l2 ->
    matchExp (eWaitTime e1 e2) (eWaitTime e1' e2') l
  | mePeriod (l : list (Var * Exp)) (e e' : Exp) :
    matchExp e e' l -> matchExp (ePeriod e) (ePeriod e') l
  | meDist (l l1 l2 : list (Var * Exp)) (e1 e2 e1' e2' : Exp) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> lubBindList l l1 l2 ->
    matchExp (eDist e1 e2) (eDist e1' e2') l
  | meFailSafeSucc (l : list (Var * Exp)) (e e' : Exp) :
    matchExp e e' l -> matchExp (eFailSafeSucc e) (eFailSafeSucc e') l.

(** There is at most one "minimal" solution to the matching problem for expressions,
as characterised by the matchExp relation.*)
Lemma matchExpUnique (e1 e2 : Exp) (l1 l2 : list (Var * Exp)) :
  matchExp e1 e2 l1 -> matchExp e1 e2 l2 -> l1 = l2. intros.
  generalize dependent l2. induction H; intros;
  try (inversion H2; eapply lubBindListUnique; [apply H1|];
  replace l1 with l4; [replace l2 with l5;[assumption|]|];
  [symmetry; eapply IHmatchExp2; assumption | symmetry; apply IHmatchExp1;
  assumption]); try (inversion H0; reflexivity); try
  (apply IHmatchExp; inversion H0; assumption). Qed.

Lemma decMatchExp (e1 e2 : Exp) :
  decidable (exists l, matchExp e1 e2 l).
  (*Just did a swap because I had matchExp matching the wrong way originally
   before I did this proof, then I changed it around, but wanted to keep the
   hard earned proof script.*)
  generalize dependent e1. induction e2; intros;
  (**For the special case where e2 is a variable.*)
  try solve [left; exists ([(v, e1)]); constructor]; destruct e1;
  (**For all the cases where the structures of e2 and e1 differ.*)
  try solve [right; unfold not; intros; inversion H; inversion H0];
  (**For the inductive case with two hypotheses*)
  try (addHyp (IHe2_1 e1_1); clear IHe2_1; rename H into Q1;
  addHyp (IHe2_2 e1_2); clear IHe2_2; rename H into Q2;
  invertClear Q1;[invertClear Q2;
  [invertClear H; invertClear H0; addHyp (decLubBindList x x0);
  invertClear H0;[invertClear H2; left; exists x1;
  (try eapply meSub; try eapply meAdd; try eapply meMult; try eapply meWaitTime;
  try eapply meDist);
  [apply H1 | apply H | assumption] |
  right; unfold not; intro; inversion H0; apply H2; inversion H3; exists x1;
  replace x with l1; [replace x0 with l2; [assumption
  | eapply matchExpUnique; [apply H10 | assumption] ]
  | eapply matchExpUnique; [apply H8 | assumption]] ]
  | right; unfold not; intros; apply H0; invertClear H1;
  invertClear H2; exists l2; assumption ]
  | right; unfold not; intros; apply H; invertClear H0;
  invertClear H1; exists l1; assumption]).
  (*Case: BaseType*)
  addHyp (eqDecBase b b0). invertClear H. left. exists (@nil (Var*Exp)).
  rewrite H0. constructor. right. unfold not. intro. inversion H.
  apply H0. inversion H1. reflexivity.
  (*Case: Period*)
  addHyp (IHe2 e1). clear IHe2. invertClear H. invertClear H0.
  left. exists x. constructor. assumption.
  right. unfold not. intro. apply H0. invertClear H. exists x.
  invertClear H1. assumption.
  (*Case Fail Safe Succ*)
  addHyp (IHe2 e1). clear IHe2. invertClear H. invertClear H0.
  left. exists x. constructor. assumption.
  right. unfold not. intro. apply H0. invertClear H. exists x.
  invertClear H1. assumption. Qed.

Lemma matchExpSubEquivPre (e1 e2 : Exp) (l l' : list (Var * Exp)) :
  matchExp e1 e2 l -> preordBindList l l' ->
  e1 = subExp (bindListToSub l') e2. intros.
  generalize dependent l'. induction H; intros; simpl;
  try (f_equal;[apply IHmatchExp1; eapply preordBindList_trans;[|apply H2];
  eapply lubPreordFst; apply H1 |
  apply IHmatchExp2; eapply preordBindList_trans;[|apply H2];
  eapply lubPreordSnd; apply H1]).
  erewrite <- preord_subst; [|apply H0|].
  rewrite bindListToSubCons. rewrite updateAppEq. reflexivity.
  rewrite splitSrcCons. constructor. reflexivity.
  reflexivity. f_equal. apply IHmatchExp. assumption.
  f_equal. apply IHmatchExp. assumption. Qed.
  
(**The free variables of an expression- drill down to all the eVar constructors.*)
Fixpoint freeVarsExp (e : Exp) : set Var :=
  match e with
  | eVar v => [v]
  | eBase b => empty_set Var
  | eSubtract e1 e2 => set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)
  | eMult e1 e2 => set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)
  | eAdd e1 e2 => set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)
  | eWaitTime e1 e2 => set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)
  | ePeriod e' => freeVarsExp e'
  | eFailSafeSucc e' => freeVarsExp e'
  | eDist e1 e2 => set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)
  end.  

Definition freeVarsListExp (l : list Exp) : set Var :=
  fold_right (set_union eqDecVar) [] (map freeVarsExp l).

Fixpoint freeVarsListExpAlt (l : list Exp) : set Var :=
  match l with
  | [] => []
  | e :: l' => set_union eqDecVar (freeVarsExp e) (freeVarsListExpAlt l')
  end.

Lemma freeVarsListAlt_correct (l : list Exp) :
  freeVarsListExp l = freeVarsListExpAlt l. induction l.
  reflexivity. simpl. unfold freeVarsListExp. simpl.
  f_equal. rewrite <- IHl. unfold freeVarsListExp.
  reflexivity. Qed.

Fixpoint freeVarsBoolExp (b : BoolExp) : set Var :=
  match b with
  | bSufficient e1 e2 => set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)
  | bNot b' => freeVarsBoolExp b'
  | bEqual e1 e2 => set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)
  | bPossInc e1 e2 e3 => set_union eqDecVar
    (set_union eqDecVar (freeVarsExp e1) (freeVarsExp e2)) (freeVarsExp e3)
  end.
  
(**TO GO: COMH BASICS.*)
Lemma in_cons_not {X : Type} (p : forall (a b : X), {a = b} + {a <> b})
  (x y : X) (l : list X) :
  x _: (y :: l) -> x = y \/ x <> y /\ x _: l. intros.
  addHyp (p x y). invertClear H0. left. assumption.
  right. inversion H. apply False_ind. apply H1. rewrite H0.
  reflexivity. split; assumption. Qed.

Lemma in_cons_not_var (x y : Var) (l : list Var) :
  x _: (y :: l) -> x = y \/ x <> y /\ x _: l. apply in_cons_not.
  apply eqDecVar. Qed.

Lemma firstOcc_res_exp_sub (v : Var) (e : Exp) (l : list (Var * Exp)) (x : list Var) :
  firstOcc v e (restrictSrc l x) -> e = (bindListToSub l) v. intros.
  induction x; inversion H. reflexivity. apply IHx. assumption. Qed.

Lemma in_firstOcc_res (v : Var) (l : list (Var * Exp)) (x : list Var) :
  v _: x -> firstOcc v ((bindListToSub l) v) (restrictSrc l x). intros.
  induction x. inversion H. simpl. apply in_cons_not_var in H.
  invertClear H. rewrite H0. constructor. invertClear H0.
  constructor; [|assumption]. apply IHx. assumption. Qed.

Lemma firstOcc_restrict_incl (v : Var) (e : Exp) (l : list (Var * Exp)) (x y : list Var) :
  firstOcc v e (restrictSrc l x) -> incl x y -> firstOcc v e (restrictSrc l y).
  intros. addHyp H. apply firstOcc_res_exp_sub in H. rewrite H.
  apply in_firstOcc_res. apply H0. apply firstOcc_splitSrc in H1.
  rewrite restrictSrc_source in H1. assumption. Qed. 

Lemma preord_res_splitSrc (l1 l2 : list (Var * Exp)) :
  l1 <[] l2 -> l1 <[] (restrictSrc l2 (splitSrc l2)).
  repeat rewrite preordBindListAlt. intros. apply H in H0.
  clear H. invertClear H0. rewrite restrictSrc_source.
  rewrite H1. split. assumption. symmetry.
  rewrite restrictSrc_incl_subEq. reflexivity.
  apply incl_refl. Qed.

Lemma preord_restrict_union1 (l l' : list (Var * Exp)) (x y : list Var) :
  l <[] restrictSrc l' x -> l <[] restrictSrc l' (set_union eqDecVar x y).
  intros. unfold preordBindList. intros. apply H in H0.
  eapply firstOcc_restrict_incl. apply H0. unfold incl.
  intros. apply set_union_intro1. apply H1. Qed.
  
Lemma preord_restrict_union2 (l l' : list (Var * Exp)) (x y : list Var) :
  l <[] restrictSrc l' y -> l <[] restrictSrc l' (set_union eqDecVar x y). 
  intros. unfold preordBindList. intros. apply H in H0.
  eapply firstOcc_restrict_incl. apply H0. unfold incl.
  intros. apply set_union_intro2. apply H1. Qed.

Lemma lub_join_preordBindList (l l' l1 l2 : list (Var * Exp)) : 
  lubBindList l l1 l2 -> joinBindList l' l1 l2 -> l <[] l'. intros.
  apply join_lubBindList_ex in H0. invertClear H0. invertClear H1.
  replace l with x. assumption. eapply lubBindListUnique.
  apply H0. assumption. Qed.

(** Any Exp e with substitution from bindList x applied can be matched by some 
bindList z to e, where z is less than x in the preorder.*)
Theorem sub_matchExp_ex (e : Exp) (l : list (Var * Exp)) :
  exists z, matchExp (subExp (bindListToSub l) e) e z
  /\ z <[] (restrictSrc l (freeVarsExp e)).
  induction e; simpl;
  (*Some processing of the inductive hypothesis for those cases with 2.*)
  try (invertClear IHe1; invertClear IHe2; rename x into l1; rename x0 into l2;
  invertClear H; invertClear H0;
  remember (freeVarsExp e1) as x; remember (freeVarsExp e2) as y;
  assert (joinBindList (restrictSrc l (set_union eqDecVar x y)) l1 l2) as Q;[
  split; [apply preord_restrict_union1;assumption|
  apply preord_restrict_union2;assumption]|];
  apply join_lubBindList_ex in Q; invertClear Q; invertClear H0;
  exists x0; split; [|assumption];
  econstructor; [apply H1 | apply H | assumption]);
  (*Some processing for the single I.H. cases*)
  try (invertClear IHe; rename x into l'; invertClear H;
  exists l'; split;[|assumption]; constructor; apply H0).
  rewrite <- bindApp_subst. exists [(v, (bindApp l v))]; split. 
  constructor. apply preordBindList_refl.
  exists (@nil (Var * Exp)). split. constructor. apply preordBindList_refl. Qed.

(** A characterisation of the matching problem for a list of expressions. This says that
the list l1 is equal to the list l2 with the substitution l applied.*)
Inductive matchExpLists : list Exp -> list Exp -> list (Var * Exp) -> Prop :=
  | melNil : matchExpLists [] [] []
  | melCons (e1 e2 : Exp) (l1 l2 : list Exp) (x1 x2 x3 : list (Var * Exp)) :
    matchExp e1 e2 x1 -> matchExpLists l1 l2 x2 -> lubBindList x3 x1 x2 ->
    matchExpLists (e1 :: l1) (e2 :: l2) x3.
  
(** A characterisation of the matching problem for a boolean expressions. This says that
the b1 equals b2 with the substitution l applied.*)
Inductive matchBoolExp : BoolExp -> BoolExp -> list (Var * Exp) -> Prop :=
  | mbeSuff (e1 e1' e2 e2' : Exp) (l l1 l2 : list (Var * Exp)) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> lubBindList l l1 l2 ->
    matchBoolExp (bSufficient e1 e2) (bSufficient e1' e2') l
  | mbeNot (b b' : BoolExp) (l : list (Var * Exp)) :
    matchBoolExp b b' l -> matchBoolExp (bNot b) (bNot b') l
  | mbeEqual (e1 e1' e2 e2' : Exp) (l l1 l2 : list (Var * Exp)) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> lubBindList l l1 l2 ->
    matchBoolExp (bEqual e1 e2) (bEqual e1' e2') l
  | mbePossInc (e1 e1' e2 e2' e3 e3' : Exp) (l l' l1 l2 l3 : list (Var * Exp)) :
    matchExp e1 e1' l1 -> matchExp e2 e2' l2 -> matchExp e3 e3' l3 ->
    lubBindList l l1 l2 -> lubBindList l' l l3 ->     
    matchBoolExp (bPossInc e1 e2 e3) (bPossInc e1' e2' e3') l'.

(** There is at most one "minimal" solution to the matching problem for
lists of expressions as characterised by the matchExpLists relation.*)
Lemma matchExpListsUnique (e1 e2 : list Exp) (l1 l2 : list (Var * Exp)) :
  matchExpLists e1 e2 l1 -> matchExpLists e1 e2 l2 -> l1 = l2. intros.
  generalize dependent l2; induction H; intros. inversion H0.
  reflexivity. inversion H2. apply IHmatchExpLists in H9.
  rewrite <- H9 in H10. replace x0 with x1 in H10.
  eapply lubBindListUnique. apply H1. assumption.
  eapply matchExpUnique. apply H. assumption. Qed.

(** There is at most one "minimal" solution to the matching problem for
boolean expressions, as characterised by the matchExp relation.*)
Lemma matchBoolExpUnique (e1 e2 : BoolExp) (l1 l2 : list (Var * Exp)) :
  matchBoolExp e1 e2 l1 -> matchBoolExp e1 e2 l2 -> l1 = l2. intros.
  induction H; inversion H0; try
  (eapply lubBindListUnique; [apply H2|]; replace l1 with l4; [replace l0 with l5;
  [apply H10|eapply matchExpUnique; [apply H9 | apply H1]]|
   eapply matchExpUnique; [apply H7 | apply H]]).
  inversion H0. apply IHmatchBoolExp. assumption.
  eapply lubBindListUnique. apply H4. replace l with l4. replace l3 with l7.
  assumption. eapply matchExpUnique. apply H14. assumption. symmetry.
  eapply lubBindListUnique. apply H3. replace l1 with l5.
  replace l0 with l6. assumption. eapply matchExpUnique.
  apply H13. assumption. eapply matchExpUnique. apply H11.
  assumption. Qed.

Lemma decMatchBoolExp (e1 e2 : BoolExp) :
  decidable (exists l, matchBoolExp e1 e2 l).
  generalize dependent e2; induction e1;
  intros; destruct e2; try solve [right; unfold not; intros;
  inversion H; inversion H0].
  (*Case: Sufficient*)
  addHyp (decMatchExp e e1). invertClear H. invertClear H0.
  addHyp (decMatchExp e0 e2). invertClear H0. invertClear H1.
  addHyp (decLubBindList x x0). invertClear H1. invertClear H2.
  left. exists x1. econstructor. apply H. apply H0. assumption.
  right. unfold not. intros. apply H2. invertClear H1.
  inversion H3. exists x1. replace x with l1. replace x0 with l2.
  assumption. eapply matchExpUnique. apply H9. assumption.
  eapply matchExpUnique. apply H7. assumption.
  right. unfold not. intros. apply H1. inversion H0. inversion H2.
  exists l2. assumption.
  right. unfold not. intros. apply H0. inversion H. inversion H1.
  exists l1. assumption.
  (*Case: Not*)
  addHyp (IHe1 e2). clear IHe1. invertClear H. invertClear H0. left.
  exists x. constructor. assumption. right. unfold not. intros.
  apply H0. invertClear H. exists x. invertClear H1. assumption.
  (*Case: Eq*)
  addHyp (decMatchExp e e1). invertClear H. invertClear H0.
  addHyp (decMatchExp e0 e2). invertClear H0. invertClear H1.
  addHyp (decLubBindList x x0). invertClear H1. invertClear H2.
  left. exists x1. econstructor. apply H. apply H0. assumption.
  right. unfold not. intros. apply H2. invertClear H1.
  inversion H3. exists x1. replace x with l1. replace x0 with l2.
  assumption. eapply matchExpUnique. apply H9. assumption.
  eapply matchExpUnique. apply H7. assumption.
  right. unfold not. intros. apply H1. inversion H0. inversion H2.
  exists l2. assumption.
  right. unfold not. intros. apply H0. inversion H. inversion H1.
  exists l1. assumption.
  (*Case: PossInc*)
  addHyp (decMatchExp e e2). invertClear H. invertClear H0.
  addHyp (decMatchExp e0 e3). invertClear H0. invertClear H1.
  addHyp (decMatchExp e1 e4). invertClear H1. invertClear H2.
  addHyp (decLubBindList x x0). invertClear H2. invertClear H3.
  addHyp (decLubBindList x2 x1). invertClear H3. invertClear H4.
  left. exists x3. econstructor. apply H. apply H0. apply H1.
  apply H2. assumption.
  right. unfold not. intros. apply H4. invertClear H3.
  inversion H5. exists x3. replace x2 with l. replace x1 with l3.
  assumption. eapply matchExpUnique. apply H14. assumption.
  eapply lubBindListUnique. apply H15. replace l1 with x. replace l2 with x0.
  assumption. eapply matchExpUnique. apply H0. assumption.
  eapply matchExpUnique. apply H. assumption.
  right. unfold not. intros. apply H3. inversion H2. inversion H4.
  exists l. replace x with l1. replace x0 with l2. assumption.
  eapply matchExpUnique. apply H13. assumption. eapply matchExpUnique.
  apply H11. assumption.
  right. unfold not. intros. apply H2. inversion H1. inversion H3.
  exists l3. assumption. 
  right. unfold not. intros. apply H1. inversion H0. inversion H2.
  exists l2. assumption.
  right. unfold not. intros. apply H0. inversion H. inversion H1.
  exists l1. assumption. Qed.

Lemma decMatchExpLists (e1 e2 : list Exp) :
  decidable (exists l, matchExpLists e1 e2 l).
  generalize dependent e2. induction e1; intros; destruct e2;
  try solve [right; unfold not; intros; inversion H; inversion H0].
  left. exists (@nil (Var*Exp)). constructor.
  addHyp (IHe1 e2). clear IHe1. invertClear H. invertClear H0.
  rename e into e'. rename a into e.
  addHyp (decMatchExp e e'). invertClear H0. invertClear H1.
  addHyp (decLubBindList x0 x). invertClear H1. invertClear H2.
  left. exists x1. econstructor. apply H0. apply H. assumption.
  right. unfold not. intros. apply H2. invertClear H1.
  invertClear H3. exists x1. replace x0 with x2. replace x with x3.
  assumption. eapply matchExpListsUnique. apply H9. assumption.
  eapply matchExpUnique. apply H7. assumption.
  right. unfold not. intros. apply H1. invertClear H0.
  invertClear H2. exists x1. assumption.
  right. unfold not. intros. apply H0. invertClear H.
  invertClear H1. exists x2. assumption. Qed.

(**TO GO: COMH BASICS*)
Lemma split_append_fst {A B : Type} (l1 l2 : list (A * B)) :
  fst (split (l1 ++ l2)) = fst (split l1) ++ fst (split l2).
  induction l1. reflexivity. destruct a. simpl.
  remember (split (l1 ++ l2)). destruct p.
  remember (split l1). destruct p. simpl. f_equal.
  apply IHl1. Qed.

(**TO GO: COMH BASICS*)
Lemma split_append_snd {A B : Type} (l1 l2 : list (A * B)) :
  snd (split (l1 ++ l2)) = snd (split l1) ++ snd (split l2).
  induction l1. reflexivity. destruct a. simpl.
  remember (split (l1 ++ l2)). destruct p.
  remember (split l1). destruct p. simpl. f_equal.
  apply IHl1. Qed.

Lemma bindSub_app_id (l1 l2 : list (Var * Exp)) :
  bindListToSub l1 = idSubst -> bindListToSub l2 = idSubst ->
  bindListToSub (l1 ++ l2) = idSubst. intros.
  apply functional_extensionality. intros.
  assert (bindListToSub l1 x = idSubst x). rewrite H. reflexivity.
  clear H. induction l1. rewrite <- H0. simpl. reflexivity.
  destruct a. rewrite <- bindApp_subst in H1. rewrite <- bindApp_subst.
  simpl. simpl in H1. remember (eqDecVar x v). rewrite <- H1.
  destruct s. reflexivity. rewrite H1. rewrite bindApp_subst.
  apply IHl1. rewrite <- bindApp_subst. assumption. Qed.
  
Lemma notIn_src_bindApp_id (x : Var) (l : list (Var * Exp)) :
  ~ x _: splitSrc l -> bindApp l x = idSubst x. intros.
  induction l. reflexivity. destruct a. simpl.
  remember (eqDecVar x v). rewrite splitSrcCons in H. destruct s.
  rewrite e0 in H. apply False_ind. apply H. 
  left. reflexivity. apply IHl. unfold not. intros.
  apply H. right. assumption. Qed.

(**TO GO: Comh Basics*)
Lemma in_sing {X : Type} (x y : X) :
  x _: [y] -> x = y. intros. inversion H. rewrite H0.
  reflexivity. inversion H0. Qed.

Lemma restrict_nil_id (l : list (Var * Exp)) (x : list Var) :
  l<[]restrictSrc [] x -> bindListToSub l = idSubst. intros.
  generalize dependent l. induction x; intros.
  apply preord_emp_eq in H. rewrite H. reflexivity.
  simpl in H. unfold bindListToSub in H. simpl in H.
  apply functional_extensionality. intros.
  addHyp (eqDecVar x0 a). invertClear H0.
  addHyp (in_dec eqDecVar a (splitSrc l)). invertClear H0.
  apply in_src_ex_firstOcc in H2. invertClear H2. addHyp H0.
  apply H in H2. apply firstOcc_bindApp in H0. rewrite bindApp_subst in H0.
  rewrite H1. rewrite H0. inversion H2. reflexivity. apply False_ind.
  apply H7. reflexivity. rewrite <- bindApp_subst. apply notIn_src_bindApp_id.
  rewrite H1. assumption. apply preord_cons_excl in H. apply IHx in H.
  rewrite <- bindApp_subst. rewrite notIn_bindApp_excl with (l2 := [a]).
  rewrite bindApp_subst. rewrite H. reflexivity. unfold not. intros.
  apply H1. apply in_sing; assumption. Qed.

Lemma matchExp_refl (e : Exp) :
  exists z, matchExp e e z /\ (bindListToSub z = idSubst).
  addHyp (sub_matchExp_ex e []). invertClear H. invertClear H0.
  exists x. rewrite idSubExp in H. split. apply H.
  eapply restrict_nil_id. apply H1. Qed.

Lemma incl_restrict_refl (l : list (Var * Exp)) (x y : list Var) :
  incl x y -> restrictSrc l x <[] restrictSrc l y. intros.
  rewrite preordBindListAlt. intros.
  assert (x0 _: x). erewrite <- restrictSrc_source. apply H0.
  assert (x0 _: y). apply H. assumption.
  assert (x0 _: splitSrc (restrictSrc l y)). rewrite restrictSrc_source.
  assumption. split. assumption. repeat (rewrite restrictSrc_in;[|assumption]).
  reflexivity. Qed.

(** Any list l with substitution from bindList x applied can be matched by some 
bindList z to l, where z is less than x in the preorder.*)
Theorem sub_matchLists_ex (l : list Exp) (x : list (Var * Exp)) :
  exists z, matchExpLists
  (listSub (bindListToSub x) l) l z /\
  preordBindList z (restrictSrc x (freeVarsListExp l)).
  induction l. exists (@nil (Var * Exp)). split. constructor.
  apply preord_emp. invertClear IHl. invertClear H. simpl.
  addHyp (sub_matchExp_ex a x). invertClear H. invertClear H2.
  apply (preord_restrict_union1 x0 x (freeVarsListExp l) (freeVarsExp a)) in H1.
  apply (preord_restrict_union2 x1 x (freeVarsListExp l) (freeVarsExp a)) in H3.
  remember (restrictSrc x (set_union eqDecVar (freeVarsListExp l) (freeVarsExp a))).
  assert (joinBindList l0 x1 x0). split; assumption. apply join_lubBindList_ex in H2.
  invertClear H2. invertClear H4. exists x2. split. econstructor.
  apply H. apply H0. assumption. eapply preordBindList_trans.
  apply H5. rewrite Heql0. apply incl_restrict_refl.
  unfold freeVarsListExp. simpl. unfold incl. intros.
  apply set_union_elim in H4. invertClear H4. apply set_union_intro2.
  assumption. apply set_union_intro1. assumption. Qed.





















Lemma joinBinList_comm (l1 l2 l3 : list (Var * Exp)) :
  joinBindList l1 l2 l3 -> joinBindList l1 l3 l2. intros.
  invertClear H. split; assumption. Qed. 

(** Any boolexp b with substitution from bindList x applied can be matched by some 
bindList z to b, where z is less than x in the preorder.*)
Theorem sub_matchBool_ex (b : BoolExp) (x : list (Var * Exp)) :
  exists z, matchBoolExp
  (subBoolExp (bindListToSub x) b) b z
  /\ preordBindList z (restrictSrc x (freeVarsBoolExp b)). induction b; simpl;
  try(
  addHyp (sub_matchExp_ex e x); addHyp (sub_matchExp_ex e0 x);
  invertClear H; invertClear H0; invertClear H1; invertClear H;
  apply (preord_restrict_union1 x0 x (freeVarsExp e) (freeVarsExp e0)) in H2;
  apply (preord_restrict_union2 x1 x (freeVarsExp e) (freeVarsExp e0)) in H3;
  remember (restrictSrc x (set_union eqDecVar (freeVarsExp e) (freeVarsExp e0)))
  as z'; assert (joinBindList z' x0 x1); [split; assumption |
  apply join_lubBindList_ex in H; invertClear H; invertClear H4;
  exists x2; split;[econstructor; [apply H0 | apply H1 | assumption] |assumption]]).
  invertClear IHb. invertClear H. exists x0. split. constructor. assumption.
  assumption.
  addHyp (sub_matchExp_ex e x); addHyp (sub_matchExp_ex e0 x);
  addHyp (sub_matchExp_ex e1 x). invertClear H; invertClear H0; invertClear H1.
  invertClear H2. invertClear H. invertClear H0.
  apply (preord_restrict_union1 x0 x (freeVarsExp e) (freeVarsExp e0)) in H3.
  apply (preord_restrict_union2 x1 x (freeVarsExp e) (freeVarsExp e0)) in H4.
  remember (restrictSrc x (set_union eqDecVar (freeVarsExp e) (freeVarsExp e0)))
  as z'. assert (joinBindList z' x0 x1). split; assumption.
  apply join_lubBindList_ex in H0. invertClear H0. invertClear H6.
  rewrite Heqz' in H7.
  apply (preord_restrict_union1 x3 x (set_union eqDecVar (freeVarsExp e) (freeVarsExp e0))
  (freeVarsExp e1)) in H7.
  apply (preord_restrict_union2 x2 x (set_union eqDecVar (freeVarsExp e) (freeVarsExp e0))
  (freeVarsExp e1)) in H5.
  remember (restrictSrc x (set_union eqDecVar (set_union eqDecVar (freeVarsExp e)
  (freeVarsExp e0)) (freeVarsExp e1))) as z''.
  assert (joinBindList z'' x3 x2). split; assumption.
  apply join_lubBindList_ex in H6. invertClear H6. invertClear H8.
  exists x4. split. econstructor. apply H1. apply H2. apply H.
  apply H0. assumption. assumption. Qed.

Lemma matchListsSubEquivPre (l1 l2 : list Exp) (z z' : list (Var * Exp)) :
  matchExpLists l1 l2 z -> preordBindList z z' ->
  l1 = listSub (bindListToSub z') l2. intro. 
  induction H; intros. reflexivity. assert (x2 <[] z' /\ x1 <[] z').
  invertClear H1. invertClear H3. split; eapply preordBindList_trans.
  apply H7. rewrite <- H5. rewrite <- H6. rewrite H4.
  assumption. apply H1. rewrite <- H5. rewrite <- H6. rewrite H4.
  assumption. invertClear H3. simpl. f_equal. eapply matchExpSubEquivPre.
  apply H. assumption. apply IHmatchExpLists. assumption. Qed.

Lemma matchListsSubEquiv (e1 e2 : list Exp) (l : list (Var * Exp)) :
  matchExpLists e1 e2 l -> e1 = listSub (bindListToSub l) e2. intros.
  eapply matchListsSubEquivPre. apply H. apply preordBindList_refl. Qed.

Lemma matchBoolExpSubEquivPre (e1 e2 : BoolExp) (l l' : list (Var * Exp)) :
  matchBoolExp e1 e2 l -> preordBindList l l' ->
  e1 = subBoolExp (bindListToSub l') e2. intros. induction H;
  try (invertClear H2; rewrite H5 in H4; rewrite H6 in H4; rewrite H4 in H3;
  clear H4 H5 H6; invertClear H3; addHyp (preordBindList_trans l1 l l' H2 H0);
  addHyp (preordBindList_trans l2 l l' H4 H0); simpl;
  f_equal; eapply matchExpSubEquivPre; [apply H | assumption | apply H1 | assumption]).
  simpl. f_equal. apply IHmatchBoolExp. assumption.
  invertClear H3. rewrite H7 in H6; rewrite H8 in H6; rewrite H6 in H5;
  clear H6 H7 H8. invertClear H5. invertClear H4. rewrite H8 in H7.
  rewrite H9 in H7. rewrite H7 in H5. clear H7 H8 H9. invertClear H5.
  addHyp (preordBindList_trans l l'0 l' H4 H0).
  addHyp (preordBindList_trans l3 l'0 l' H7 H0).
  addHyp (preordBindList_trans l2 l l' H6 H5).
  addHyp (preordBindList_trans l1 l l' H3 H5).
  simpl. f_equal; eapply matchExpSubEquivPre. apply H. assumption.
  apply H1. assumption. apply H2. assumption. Qed.

Lemma subExp_restrict_eq (l1 l2 : list (Var * Exp)) (e : Exp) :
  subExp (bindListToSub l2) e = subExp (bindListToSub l1) e -> 
  subExp (bindListToSub l2) e =
  subExp (bindListToSub (restrictSrc l1 (splitSrc l2))) e. intros.
  induction e; simpl; try reflexivity; try
  (inversion H; (f_equal;[apply IHe1 | apply IHe2]);assumption).
  addHyp (in_dec eqDecVar v (splitSrc l2)).
  invertClear H0. rewrite restrictSrc_in; assumption.
  addHyp H1. rewrite <- (restrictSrc_source l1 (splitSrc l2)) in H0.
  repeat (rewrite <- notIn_bindList_id;[|assumption]). reflexivity.
  f_equal. apply IHe. inversion H. reflexivity.
  f_equal. apply IHe. inversion H. reflexivity. Qed.

Lemma subBoolExp_restrict_eq (l1 l2 : list (Var * Exp)) (b : BoolExp) :
  subBoolExp (bindListToSub l2) b = subBoolExp (bindListToSub l1) b ->
  subBoolExp (bindListToSub l2) b =
  subBoolExp (bindListToSub (restrictSrc l1 (splitSrc l2))) b.
  intros. induction b; simpl; inversion H; f_equal;
  try (apply subExp_restrict_eq; assumption).
  apply IHb. assumption. Qed.

Lemma listSub_restrict_eq (l1 l2 : list (Var * Exp)) (l : list Exp) :
  listSub (bindListToSub l2) l = listSub (bindListToSub l1) l ->
  listSub (bindListToSub l2) l =
  listSub (bindListToSub (restrictSrc l1 (splitSrc l2))) l. intros.
  induction l. reflexivity. simpl. f_equal. invertClear H.
  apply subExp_restrict_eq; assumption. apply IHl.
  inversion H. reflexivity. Qed.
 
(** Exclude distributes over restrict*)
Lemma res_excl_distr (l1 l2 : list (Var * Exp)) (l : list Var) :
  restrictSrc (excludeSrc l1 l) (splitSrc (excludeSrc l2 l)) =
  excludeSrc (restrictSrc l1 (splitSrc l2)) l.
  induction l2. reflexivity. simpl. destruct a;
  rewrite splitSrcCons. simpl. remember (in_dec eqDecVar v l).
  destruct s. assumption. rewrite splitSrcCons. simpl.
  f_equal. f_equal. repeat rewrite <- bindApp_subst.
  symmetry. apply notIn_bindApp_excl. assumption.
  assumption. Qed.

Lemma in_exclude_sub_eq (v : Var) (x : list Var) (l : list (Var * Exp)) :
  v _: x -> bindListToSub (excludeSrc l x) v = v. intros.
  rewrite <- bindApp_subst. cut (bindApp (excludeSrc l x) v = idSubst v).
  intros. unfold idSubst in H0. apply H0. apply notIn_src_bindApp_id.
  apply exclude_in_splitSrc. assumption. Qed.

(** passiveSrc x l, read x is passive in the source of l, or just x is passive in l,
means that all variables in x are only mapped to themselves by l.*)
Inductive passiveSrc : list Var -> list (Var * Exp) -> Prop :=
  | psrcEmp (l : list (Var * Exp)) : passiveSrc [] l
  | psrcConsFstOcc (x : list Var) (v : Var) (l : list (Var * Exp)) :
    passiveSrc x l -> firstOcc v (eVar v) l -> passiveSrc (v :: x) l
  | psrcConsNotIn (x : list Var) (v : Var) (l : list (Var * Exp)) :
    passiveSrc x l -> ~v _: (splitSrc l) -> passiveSrc (v :: x) l.

Lemma passive_nil (x : list Var) : passiveSrc x []. induction x. constructor.
  apply psrcConsNotIn. assumption. unfold not. intros. inversion H. Qed.

Lemma passive_tl (a : Var) (x : list Var) (l : list (Var * Exp)) : 
  passiveSrc (a :: x) l -> passiveSrc x l. intros. inversion H; assumption.
  Qed.

Lemma passive_cons_eq (v : Var) (x : list Var) (l : list (Var * Exp)) : 
  passiveSrc x l -> passiveSrc x ((v, eVar v) :: l). intros.
  induction x. constructor. addHyp (eqDecVar a v). invertClear H0.
  rewrite H1. eapply psrcConsFstOcc. apply IHx. eapply passive_tl;apply H.
  constructor. inversion H. constructor. apply IHx. assumption.
  constructor;assumption. apply psrcConsNotIn. apply IHx. assumption.
  unfold not. intros. rewrite splitSrcCons in H6. inversion H6.
  apply H1. symmetry. assumption. apply H5. assumption. Qed.

(**To Go: COMH BASICS*)
Lemma notIn_cons {X : Type} (x y : X) (l : list X) : 
  ~ x _: (y :: l) -> ~ x _: l. intros. unfold not. intros. apply H.
  apply in_cons. assumption. Qed.

Lemma passive_cons_notIn (v : Var) (e : Exp) (x : list Var) (l : list (Var * Exp)) : 
  passiveSrc x l -> ~v _: x -> passiveSrc x ((v, e) :: l). intros.
  induction x. constructor. inversion H. constructor. apply IHx.
  assumption. eapply notIn_cons. apply H0. constructor. assumption.
  unfold not. intros. apply H0. left. assumption. apply psrcConsNotIn.
  apply IHx. assumption. eapply notIn_cons. apply H0. unfold not.
  intros. apply H5. rewrite splitSrcCons in H6. invertClear H6.
  apply False_ind. apply H0. left. symmetry. assumption.
  apply H7. Qed.

Lemma notIn_src_excl (v : Var) (x : list Var) (l : list (Var * Exp)) :
  ~ v _: splitSrc l -> 
  bindListToSub (excludeSrc l (v :: x)) = bindListToSub (excludeSrc l x).
  intros. induction l. reflexivity. destruct a. rewrite splitSrcCons in H.
  assert (bindListToSub (excludeSrc l (v :: x)) = bindListToSub (excludeSrc l x)).
  apply IHl. unfold not. intros. apply H. right. assumption. clear IHl.
  simpl. remember (eqDecVar v v0). destruct s. remember (in_dec eqDecVar v0 x).
  destruct s. apply H0. rewrite e0 in H. apply False_ind. apply H. left.
  reflexivity. remember (in_dec eqDecVar v0 x). destruct s. apply H0.
  repeat rewrite bindListToSubCons. f_equal. assumption. Qed.

(** If all members of x are mapped to themselves by l, then x is passive in l.*)
Lemma idSrc_passive (x : list Var) (l : list (Var * Exp)) :
  (forall v : Var, v _: x -> (bindListToSub l) v = eVar v) ->
  passiveSrc x l. intros. induction x. constructor.
  assert ((forall v : Var, v _: x -> bindListToSub l v = v)). intros.
  apply H. right. assumption. apply IHx in H0. clear IHx.
  addHyp (in_dec eqDecVar a (splitSrc l)). invertClear H1.
  apply splitSrc_firstOcc_ex in H2. invertClear H2. addHyp H1.
  apply firstOcc_bindApp in H1. rewrite bindApp_subst in H1.
  assert (bindListToSub l a = a). apply H. left. reflexivity.
  rewrite H3 in H1. rewrite <- H1 in H2. clear H1 H3.
  constructor; assumption. apply psrcConsNotIn; assumption. Qed.

(** If x is passive in l, then excluding it from l yields the same substitution
function, and vice versa.*)
Theorem passiveSrc_exclude_equiv (x : list Var) (l : list (Var * Exp)) :
  passiveSrc x l <-> bindListToSub (excludeSrc l x) = bindListToSub l.
  split; intros. induction x. rewrite exclude_nil. reflexivity.
  apply functional_extensionality. intros. inversion H.
  rewrite <- IHx; [|assumption]. 
  addHyp (in_dec eqDecVar x0 (a :: x)). invertClear H5.
  rewrite in_exclude_sub_eq; [|assumption]. inversion H6.
  rewrite IHx;[|assumption]. repeat rewrite <- H5. 
  apply firstOcc_bindApp in H4. rewrite <- bindApp_subst. rewrite H4.
  reflexivity. rewrite in_exclude_sub_eq; [|assumption]. reflexivity.
  assert (~ x0 _: x). unfold not. intros. apply H6. right. assumption.
  repeat rewrite <- bindApp_subst.
  repeat (rewrite <- notIn_bindApp_excl; [|assumption]). reflexivity.
  rewrite notIn_src_excl. rewrite IHx. reflexivity. assumption.
  assumption.
  (*Right to left*)
  apply idSrc_passive. intros. rewrite <- H. apply in_exclude_sub_eq.
  assumption. Qed.

Theorem dec_passiveSrc (x : list Var) (l : list (Var * Exp)) :
  decidable (passiveSrc x l). induction x. left. constructor.
  invertClear IHx. addHyp (in_dec eqDecVar a (splitSrc l)).
  invertClear H0. addHyp H1. apply splitSrc_firstOcc_ex in H0.
  invertClear H0. addHyp (eqDecExp a x0). invertClear H0.
  left. rewrite <- H3 in H2. constructor; assumption.
  right. unfold not. intros. inversion H0. apply H3.
  eapply firstOcc_unique. apply H8. assumption.
  apply H8. assumption. left. apply psrcConsNotIn; assumption.
  right. unfold not. intros. apply H. eapply passive_tl.
  apply H0. Qed.

Lemma passive_in_firstOcc_eq (v : Var) (e : Exp) (x : list Var)
  (l : list (Var * Exp)) :
  passiveSrc x l -> v _: x -> firstOcc v e l -> e = eVar v.
  intros. induction H. inversion H0. apply in_cons_not_var in H0.
  invertClear H0. eapply firstOcc_unique. apply H1. repeat rewrite H3.
  assumption. invertClear H3. apply IHpassiveSrc; assumption.
  apply in_cons_not_var in H0.
  invertClear H0. apply False_ind. apply H2. rewrite <- H3.
  eapply firstOcc_splitSrc. apply H1. invertClear H3.
  apply IHpassiveSrc; assumption. Qed.

Lemma in_firstOcc_id (v : Var) (x : list Var) :
  v _: x -> firstOcc v v (idBindList x). intros. induction x.
  inversion H. apply in_cons_not_var in H. invertClear H.
  simpl. repeat rewrite H0. constructor. invertClear H0.
  simpl. constructor. apply IHx. assumption. assumption. Qed.

Lemma firstOcc_notIn_append (v : Var) (e : Exp) (l1 l2 : list (Var * Exp)) :
  firstOcc v e l2 -> ~v _: (splitSrc l1) -> firstOcc v e (l1 ++ l2). intros.
  induction l1. apply H. destruct a. assert (~ v _: splitSrc l1). unfold not.
  intros. apply H0. rewrite splitSrcCons. right. assumption. apply IHl1 in H1.
  simpl. constructor. assumption. unfold not. intro. apply H0.
  rewrite splitSrcCons. left. rewrite H2. reflexivity. Qed.

Lemma passive_excl_id (x : list Var) (l l' : list (Var * Exp)) :
  passiveSrc x l -> (excludeSrc l x) <[] l' ->
  l <[] (idBindList x) ++ l'. intros. unfold preordBindList. intros.
  addHyp (in_dec eqDecVar x0 x). invertClear H2.
  assert (e = eVar x0). eapply passive_in_firstOcc_eq.
  apply H. assumption. assumption. rewrite H2. clear H2.
  apply firstOcc_append. apply in_firstOcc_id. assumption.
  apply firstOcc_notIn_append. apply H0.
  apply firstOcc_notIn_exclude; assumption. rewrite srcIdBindList.
  assumption. Qed.

Lemma notEq_sub_excl_eq (v v' : Var) (x : list Var) (l : list (Var * Exp)) :
  v <> v' -> bindListToSub (excludeSrc l x) v' =
  bindListToSub (excludeSrc l (v :: x)) v'. intros. induction l.
  reflexivity. destruct a. simpl. remember (in_dec eqDecVar v0 x).
  destruct s. remember (eqDecVar v v0). destruct s. apply IHl.
  apply IHl. remember (eqDecVar v v0). destruct s.
  rewrite bindListToSubCons. rewrite <- e0.
  rewrite updateAppNeq;[|assumption]. apply IHl.
  repeat rewrite bindListToSubCons. addHyp (eqDecVar v0 v').
  invertClear H0. repeat rewrite H1. repeat rewrite updateAppEq.
  reflexivity. repeat (rewrite updateAppNeq;[|assumption]).
  apply IHl. Qed.

Lemma id_app_excl_sub_eq (x : list Var) (l : list (Var * Exp)) :
  bindListToSub (idBindList x ++ l) = bindListToSub (excludeSrc l x).
  apply functional_extensionality. intros.
  induction x. rewrite exclude_nil. reflexivity.
  simpl. rewrite bindListToSubCons. addHyp (eqDecVar a x0).
  invertClear H. rewrite H0. rewrite updateAppEq.
  rewrite in_exclude_sub_eq. reflexivity. left. reflexivity.
  rewrite updateAppNeq;[|assumption]. rewrite IHx.
  apply notEq_sub_excl_eq. assumption. Qed.

Lemma excludeSrc_idem (x : list Var) (l : list (Var * Exp)) :
  (excludeSrc l x) = (excludeSrc (excludeSrc l x) x). induction l.
  reflexivity. destruct a. simpl. remember (in_dec eqDecVar v x).
  destruct s. assumption. simpl. remember (in_dec eqDecVar v x).
  destruct s. apply False_ind. apply n. assumption.
  f_equal. assumption. Qed.

Lemma notIn_restrict (v : Var) (x : list Var) (l : list (Var * Exp)) :
  ~ v _: x -> bindListToSub (restrictSrc l x) v = v. intros.
  induction x. reflexivity. addHyp H. apply notIn_cons in H.
  apply IHx in H. clear IHx. simpl. rewrite <- bindApp_subst.
  simpl. remember (eqDecVar v a). destruct s. apply False_ind.
  apply H0. left. rewrite e. reflexivity. rewrite bindApp_subst.
  assumption. Qed.

Lemma pre_excl_res_id (v : Var) (x w : list Var)
  (l1 l2 : list (Var * Exp)) :
  l1 <[] (restrictSrc (excludeSrc l2 x) w) -> v _: x ->
  (bindListToSub l1) v = v.
  intros. rename H0 into Q. rewrite preordBindListAlt in H.
  addHyp (in_dec eqDecVar v (splitSrc l1)).
  invertClear H0. apply H in H1. invertClear H1. rewrite H2.
  addHyp (in_dec eqDecVar v w). invertClear H1.
  rewrite restrictSrc_in;[|assumption]. apply in_exclude_sub_eq.
  assumption. apply notIn_restrict; assumption.
  symmetry. apply notIn_bindList_id. assumption. Qed.

Lemma pre_excl_res_passive (x w : list Var)
  (l1 l2 : list (Var * Exp)) :
  l1 <[] (restrictSrc (excludeSrc l2 x) w) ->
  passiveSrc x l1. intros. apply idSrc_passive. intros.
  eapply pre_excl_res_id. apply H. assumption. Qed.

Lemma preordBindList_cons (a : Var * Exp) (l l' : list (Var * Exp)):
  l <[] l' -> a :: l <[] a :: l'. unfold preordBindList. intros.
  inversion H0. constructor. constructor. apply H. assumption.
  assumption. Qed.
  
Lemma exclude_restrict_cons (v : Var) (e : Exp) (x w : list Var) (l : list (Var * Exp)) :
  v _: x -> excludeSrc (restrictSrc ((v, e) :: l) w) x = excludeSrc (restrictSrc l w) x.
  induction w. reflexivity. simpl. remember (in_dec eqDecVar a x). destruct s.
  assumption. intros. addHyp H. apply IHw in H.
  replace (bindListToSub ((v, e) :: l) a) with
  (bindListToSub l a). f_equal. assumption. rewrite bindListToSubCons.
  rewrite updateAppNeq. reflexivity. unfold not. intros. apply n.
  rewrite <- H1. assumption. Qed.

Lemma notIn_sub_excl (v : Var) (x : list Var) (l : list (Var * Exp)) :
  ~v _: x -> bindListToSub (excludeSrc l x) v = bindListToSub l v.
  intros. repeat rewrite <- bindApp_subst. rewrite <- notIn_bindApp_excl.
  reflexivity. assumption. Qed.

Lemma excl_res_distr (x w : list Var) (l : list (Var * Exp)) :
  excludeSrc (restrictSrc (excludeSrc l x) w) x = excludeSrc (restrictSrc l w) x.
  induction w. reflexivity. simpl. remember (in_dec eqDecVar a x).
  destruct s. assumption. f_equal. f_equal. apply notIn_sub_excl. assumption.
  assumption. Qed.

(********Equivalence stuff***************)


Definition set_equal {A : Type} (l1 l2 : set A) : Prop :=
  forall a : A, a _: l1 <-> a _: l2.
Notation "a ={}= b" := (set_equal a b) (at level 70).

Lemma set_equal_not {A : Type} (l1 l2 : set A) : 
  l1 ={}= l2  -> forall a : A, ~a _: l1 <-> ~a _: l2. intros.
  addHyp (H a). invertClear H0. 
  unfold not; split; intros; apply H0. apply H2.
  assumption. apply H1. assumption. Qed.

Lemma set_equal_refl {A : Type} (l : set A) : 
  l ={}= l. unfold set_equal. intros. reflexivity. Qed.

Lemma set_equal_trans {A : Type} (l1 l2 l3 : set A) : 
  l1 ={}= l2  -> l2 ={}= l3  -> l1 ={}= l3. intros.
  unfold set_equal. intros. addHyp (H a). addHyp (H0 a).
  clear H H0. rewrite H1. assumption. Qed.

Lemma set_equal_symm {A : Type} (l1 l2 : set A) : 
  l1 ={}= l2  -> l2 ={}= l1. unfold set_equal. intros.
  symmetry. apply H. Qed.

Lemma set_equal_nil_l {A : Type} (l2 : set A) : 
  [] ={}= l2  -> l2 = []. intros. destruct l2.
  reflexivity. cut (a _: []). intros. inversion H0.
  addHyp (H a). rewrite H0. left. reflexivity. Qed.

Lemma set_equal_nil_r {A : Type} (l1 : set A) : 
  l1 ={}= []  -> l1 = []. intros. apply set_equal_symm in H.
  apply set_equal_nil_l. assumption. Qed.

Lemma set_equal_union_app {A : Type} (p : forall a b : A, {a = b} + {a <> b})
  (l1 l2 : set A) : 
  set_union p l1 l2 ={}= l1 ++ l2. unfold set_equal. intros. split; intros.
  apply set_union_elim in H. apply in_or_app. apply H.
  apply set_union_intro. apply in_app_or. apply H. Qed.

Definition equivBindList (l1 l2 : list (Var * Exp)) : Prop :=
  l1 <[] l2 /\ l2 <[] l1.
Notation "a =[]= b" := (equivBindList a b) (at level 70).

Lemma equiv_preordBindList_l (l1 l1' l2 : list (Var * Exp)) : 
  l1 <[] l2 -> l1 =[]= l1' -> l1' <[] l2. intros. invertClear H0.
  eapply preordBindList_trans. apply H2. assumption. Qed.

Lemma equiv_preordBindList_r (l1 l2 l2' : list (Var * Exp)) : 
  l1 <[] l2 -> l2 =[]= l2' -> l1 <[] l2'. intros. invertClear H0.
  eapply preordBindList_trans. apply H. assumption. Qed.

Lemma equivBindList_symm (l1 l2 : list (Var * Exp)) : 
  l1 =[]= l2 -> l2 =[]= l1. intros. invertClear H.
  split; assumption. Qed.

Lemma equivBindList_trans (l1 l2 l3 : list (Var * Exp)) : 
  l1 =[]= l2 -> l2 =[]= l3 -> l1 =[]= l3. intros. 
  apply equivBindList_symm in H. split.
  eapply equiv_preordBindList_l;[|apply H]. invertClear H0.
  assumption. eapply equiv_preordBindList_r;[|apply H].
  invertClear H0. assumption. Qed.
  
Lemma equivBindList_refl (l : list (Var * Exp)) : 
  l =[]= l. split; apply preordBindList_refl. Qed.

Lemma firstOcc_exclude_notIn (v : Var) (e : Exp) (x : list Var)
  (l : list (Var * Exp)) :
  firstOcc v e (excludeSrc l x) -> ~ v _: x. intros.
  addHyp (in_dec eqDecVar v x). invertClear H0.
  apply exclude_in_splitSrc with (l := l) in H1. unfold not.
  intros. apply H1. eapply firstOcc_splitSrc. apply H.
  assumption. Qed.

Lemma preord_exclude_pres (l l' : list (Var * Exp)) (x : list Var) :
  l <[] l' -> excludeSrc l x <[] excludeSrc l' x. intros.
  unfold preordBindList. intros. addHyp H0. apply exclude_firstOcc in H0.
  apply H in H0. apply firstOcc_exclude_notIn in H1.
  apply firstOcc_notIn_exclude; assumption. Qed. 

Lemma equivBindList_cons (a : Var * Exp) (l l' : list (Var * Exp)):
  l =[]= l' -> a :: l =[]= a :: l'. intros. split;
  apply preordBindList_cons; apply H. Qed.

Lemma equivBindList_exclude (l l' : list (Var * Exp)) (x : list Var) : 
  l =[]= l' -> excludeSrc l x =[]= excludeSrc l' x. intros.
  invertClear H. split; apply preord_exclude_pres; assumption. Qed.
  
Lemma equivBindList_splitSrc (l l' : list (Var * Exp)) : 
  l =[]= l' -> splitSrc l ={}= splitSrc l'. intros.
  invertClear H. rewrite preordBindListAlt in H0, H1.
  unfold set_equal. intros. addHyp (H0 a). addHyp (H1 a).
  clear H0 H1. split. intros. apply H in H0. invertClear H0.
  assumption. intros. apply H2 in H0. invertClear H0.
  assumption. Qed.

Lemma equivBindList_join (l l' l1 l2 : list (Var * Exp)) : 
  l =[]= l' -> joinBindList l l1 l2 -> joinBindList l' l1 l2.
  intros. split;
  (eapply equiv_preordBindList_r; [apply H0 | apply H]). Qed.

Lemma equivBindList_restrict (l l' : list (Var * Exp)) (x : list Var) : 
  l =[]= l' -> restrictSrc l x = restrictSrc l' x. intros.
  addHyp H. rename H0 into Q. apply equivBindList_splitSrc in Q.
  invertClear H. rewrite preordBindListAlt in H0, H1.
  induction x. reflexivity. simpl. f_equal; [| assumption].
  f_equal. addHyp (H0 a). addHyp (H1 a). clear H0 H1.  
  addHyp (in_dec eqDecVar a (splitSrc l)).
  invertClear H0. apply H. assumption. addHyp H1.
  rewrite set_equal_not in H0;[|apply Q].
  repeat (rewrite <- notIn_bindList_id;[|assumption]).
  reflexivity. Qed.

Lemma set_eq_excl (l : list (Var * Exp)) (x y : list Var) :
  x ={}= y -> excludeSrc l x = excludeSrc l y. intros.
  induction l. reflexivity. simpl. destruct a.
  remember (in_dec eqDecVar v x). destruct s.
  remember (in_dec eqDecVar v y). destruct s. assumption.
  clear Heqs. rewrite (H v) in i. apply False_ind. apply n.
  assumption. remember (in_dec eqDecVar v y). destruct s.
  clear Heqs0. apply H in i. apply False_ind. apply n.
  assumption. f_equal. assumption. Qed.

Lemma set_eq_res_preord (l : list (Var * Exp)) (x y : list Var) :
  x ={}= y -> restrictSrc l x <[] restrictSrc l y. intros.
  rewrite preordBindListAlt. intros. rewrite restrictSrc_source in H0.
  addHyp H0. apply H in H1. split. rewrite restrictSrc_source.
  assumption. repeat (rewrite restrictSrc_in;[|assumption]).
  reflexivity. Qed. 

Lemma set_eq_res_equiv (l : list (Var * Exp)) (x y : list Var) :
  x ={}= y -> restrictSrc l x =[]= restrictSrc l y. intros.
  split; apply set_eq_res_preord. assumption. apply set_equal_symm.
  assumption. Qed.

Lemma set_eq_freeVars_map (x : list Var) :
  (freeVarsListExp (map eVar x)) ={}= x. induction x.
  unfold freeVarsListExp. simpl. apply set_equal_refl.
  unfold freeVarsListExp. simpl. unfold set_equal. intros.
  split; intros. apply set_union_elim in H. invertClear H.
  apply in_sing in H0. left. symmetry. assumption. right.
  apply IHx. apply H0. apply in_cons_not_var in H. invertClear H.
  apply set_union_intro1. left. symmetry. assumption.
  apply set_union_intro2. apply IHx. invertClear H0.
  assumption. Qed.

Lemma firstOcc_in_src (v : Var) (e : Exp) (x : list Var) (l : list (Var * Exp)) : 
  firstOcc v e (restrictSrc l x) -> v _: x. intros. induction x. inversion H.
  simpl in H. inversion H. left. reflexivity. right. apply IHx. assumption. Qed.

Lemma restrict_add_cons_equiv (v : Var) (x : list Var) (l : list (Var * Exp)) :   
  restrictSrc l (set_add eqDecVar v x) =[]= restrictSrc l (v :: x).
  apply set_eq_res_equiv. unfold set_equal. intros. split; intros.
  apply set_add_elim in H. invertClear H. left. symmetry. assumption.
  right. assumption. apply in_cons_not_var in H. invertClear H.
  rewrite H0. apply set_add_intro. left. reflexivity.
  invertClear H0. apply set_add_intro. right. assumption. Qed.

Lemma diff_restrict_exclude (l : list (Var * Exp)) (x y : list Var) :
  restrictSrc l (set_diff eqDecVar x y) =[]= (excludeSrc (restrictSrc l x) y).
  induction x. apply equivBindList_refl. simpl. remember (set_mem eqDecVar a y).
  destruct b. remember (in_dec eqDecVar a y). destruct s.
  apply IHx. apply False_ind. apply n. eapply set_mem_correct1.
  symmetry. apply Heqb. remember (in_dec eqDecVar a y).
  destruct s. apply False_ind. symmetry in Heqb.
  apply set_mem_complete1 in Heqb. apply Heqb. apply i.
  eapply equivBindList_trans; [apply restrict_add_cons_equiv|].
  simpl. apply equivBindList_cons. assumption. Qed.
  
(********END: Equivalence stuff***************)

Lemma preord_restrict_app_join (x w : list Var) (l l1 l2 : list (Var * Exp)) :
  l1 <[] restrictSrc l x -> l2 <[] restrictSrc l w ->
  joinBindList (restrictSrc l (x ++ w)) l1 l2. intros.
  apply (preord_restrict_union1 l1 l x w) in H.
  apply (preord_restrict_union2 l2 l x w) in H0.
  eapply equivBindList_join;[|split;[apply H | apply H0]].
  apply set_eq_res_equiv. apply set_equal_union_app. Qed.


(*********** END: Matching Stuff.*************)

(*LOCAL TIDY*)

Lemma listSub_emp_id l : listsToSub l [] = idSubst. induction l.
  reflexivity. simpl. reflexivity. Qed.

Lemma resetSub_neq s v1 v2 :
  v1 <> v2 -> (resetSub s [v1]) v2 = s v2. intros.
  unfold resetSub. remember (inVarList v2 [v1]). destruct b.
  symmetry in Heqb. rewrite inVarList_in in Heqb. apply in_sing in Heqb.
  apply False_ind. apply H. symmetry. assumption. reflexivity. Qed.

Lemma varEq_eq x a : true = varEq x a <-> x = a. unfold varEq.
  remember (varEqDec x a). destruct s. split; intro. assumption. 
  reflexivity. split; intro. inversion H. apply False_ind.
  apply n. assumption. Qed.

Lemma varEq_neq x a : false = varEq x a <-> x <> a.
  remember (varEq x a). destruct b. split; intro. inversion H.
  rewrite varEq_eq in Heqb. apply False_ind. apply H. assumption.
  split; intro. unfold varEq in Heqb. remember (varEqDec x a).
  destruct s. inversion Heqb. assumption. reflexivity. Qed.

Lemma inVarList_out (x : Var) (l : list Var) :
  inVarList x l = false <-> ~ x _: l. split; intros.
  induction l. apply in_nil. simpl in H. remember (varEq x a).
  destruct b. inversion H. apply IHl in H. unfold not. intro.
  rewrite varEq_neq in Heqb. inversion H0. rewrite H1 in Heqb.
  apply Heqb. reflexivity. apply H. assumption.
  induction l. reflexivity. lets NI : H. apply notIn_cons in NI.
  apply IHl in NI. clear IHl. simpl. remember (varEq x a).
  destruct b. rewrite varEq_eq in Heqb. rewrite Heqb in H.
  apply False_ind. apply H. apply in_eq. assumption. Qed.

Lemma resetSub_eq s v : (resetSub s [v]) v = v. unfold resetSub.
  remember (inVarList v [v]). destruct b. reflexivity. symmetry in Heqb.
  rewrite inVarList_out in Heqb. apply False_ind. apply Heqb.
  apply in_eq. Qed.

(** Replace a single true varEqDec*)
Ltac varEqDec_true := let U := fresh in
  match goal with [ |- context[varEqDec ?x ?x]] => 
    remember (varEqDec x x) as U;
    match goal with [U1 : U = varEqDec x x |- _] =>
      clear U1; destruct U;[
      match goal with [U2 : x = x |- _] =>
        clear U2
      end |
      match goal with [U2 : x <> x |- _] =>
        contradiction U2; reflexivity
      end]
    end
  end.

(** Replace a single false varEqDec. The tactic will fail if it matches an x and a y
that aren't obviously false by inversion.*)
Ltac varEqDec_false := let U := fresh in
  match goal with [ |- context[varEqDec ?x ?y]] => 
    remember (varEqDec x y) as U;
    match goal with [U1 : U = varEqDec x y |- _] =>
      clear U1; destruct U;[
      match goal with [U2 : x = y |- _] =>
        inversion U2
      end |
      match goal with [U2 : x <> y |- _] =>
        clear U2
      end]
    end
  end.

(** Gets rid of lingering occurrences of resetSub in the goal.*)
Ltac remove_resets := simpl; repeat rewrite resetPreservesId;
  unfold idSubst; simpl; unfold liftVarList; unfold resetSub;
  simpl; unfold varEq; repeat varEqDec_true; repeat varEqDec_false.

(** Gets rid of lingering occurrences of update in the goal.*)
Ltac remove_updates := repeat (repeat rewrite updateAppEq;
  repeat (rewrite updateAppNeq;[ | solve [neq_inversion]]));
  unfold idSubst.

(** Gets rid of lingering occurrences of resetSub in the hypothesis. Tactic will
halt as soon as it encounters a resetSub that can't be eliminated, so doesn't
necessarily remove ALL possible resets from all hypotheses.*)
Ltac remove_resets_hyp U := generalize dependent U; remove_resets; intro U.

(** Gets rid of lingering occurrences of resetSub in the hypothesis.*)
Ltac remove_updates_hyp U := generalize dependent U; remove_updates; intro U.

(** Performs some simplifications to goal like removing updates and resets.*)
Ltac clean_proc := simpl; remove_resets; remove_updates.

(** If there's one hypothesis U (usually without any dependencies), this tactic
generalises it, applys some tactic t, and then re-assumed the hypothesis into the
hypotheses.*)
Ltac gen_app_intro t U := generalize dependent U; t; intro U.

Ltac clean_proc_hyp U := gen_app_intro clean_proc U.
 
(**If an expression evaluates to some b, then applying a substitution to this expression
leaves it unchanged. The intuition is that evaluation entails no free variables.*)
Lemma eval_pres_sub e b s : e |_| b -> subExp s e = e. intros. induction H; simpl;
  try (rewrite IHevalExp1; rewrite IHevalExp2); try rewrite IHevalExp; reflexivity.
  Qed.

(** The same for an expression that evaluates to a time.*)
Lemma subExp_eval_id (s : Subst) (e : Exp) (t : Time) :
  evalExpFunTime e = Some t -> subExp s e = e.
Proof.
  intro E. destruct (evalExpFunTime_some _ _ E) as [b Eb].
  apply (eval_pres_sub e b s). apply evalExpFunRel. exact Eb.
Qed.

(** A stronger version of the uniqueness property of the evalution relation over
expressions. In this version, any substitution is allowed to be applied to the
expression in one of the evaluations and the equality still holds.*)
Lemma evalExp_sub_unique_strong e b b' s : e |_| b -> subExp s e |_| b' -> b = b'.
  intros. eapply evalExpUnique. apply H. erewrite eval_pres_sub in H0.
  assumption. apply H. Qed.

(** Repeatedly matches the goal to matching evaluations, creates the equality that the
corresponding base type are equal, inverts this to unpackage the contents of the base
types, and clear the original evaluations.*)
Ltac unique_exps := repeat let U := fresh in 
  match goal with
  | [ U1 : ?e1 |_| ?b1, U2 : ?e1 |_| ?b2 |- _] =>
    assert (b1 = b2) as U;
    [eapply evalExpUnique; [apply U1 | apply U2] | ]; clear U1 U2; invertClear U
  | [ U1 : ?e1 |_| ?b1, U2 : subExp _ ?e1 |_| ?b2 |- _] =>
    assert (b1 = b2) as U;
    [eapply evalExp_sub_unique_strong; [apply U1 | apply U2] | ]; clear U1 U2;
    invertClear U
  end.

(** Given a goal of type a _: l, this tactic repeatedly checks if a is the head of l,
drilling into l until either the empty list is reached, in which case the tactic fails,
or the value a is found, in which case it proceeds with the constructor*)
Ltac inList_in_tac := match goal with
  | [ |- ?a _: (?a :: _)] => apply in_eq
  | [ |- _ _: (_ :: _)] => apply in_cons; inList_in_tac
  end.

Lemma cons_notIn {T : Type} (a b : T) l : b <> a -> ~b _: l -> ~b _: (a :: l).
  unfold not. intros. inversion H1. apply H. symmetry. assumption.
  apply H0. assumption. Qed.

(** Given a goal of type ~a _: l, this tactic repeatedly checks if a is the head of l,
drilling into l until either the empty list is reached, in which case the tactic fails,
or the value a is found, in which case it proceeds with the constructor*)
Ltac inList_out_tac := match goal with
  | [ |- ~_ _: []] => apply in_nil
  | [ |- ~_ _: (_ :: _)] => apply cons_notIn; [neq_inversion | inList_out_tac]
  end.

Ltac baseEq_aux U := intro U; inversion U; reflexivity.

Ltac baseEq := match goal with [|- ?x = ?y] =>
  let U := fresh in
  match type of x with
  | Mode => cut (baseMode x = baseMode y);[baseEq_aux U | ]
  | Time => cut (baseTime x = baseTime y);[baseEq_aux U | ]
  | Position => cut (basePosition x = basePosition y);[baseEq_aux U | ]
  | Distance => cut (baseDistance x = baseDistance y);[baseEq_aux U | ]
  | Delay => cut (baseDelay x = baseDelay y);[baseEq_aux U | ]
  | nonnegreal => cut (baseNonneg x = baseNonneg y);[baseEq_aux U| ]
  | _ => (progress repeat f_equal); baseEq
  end
  end.

(*-LOCAL TIDY*)