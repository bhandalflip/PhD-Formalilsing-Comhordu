
(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** This file contains generic tactics for making the proofs more concise. Some of these
are truly generic e.g. eliminating conjunctions, others are more speicialised for this
development.*)

(*TO DO: TIDY & ORGANISE THIS FILE A BIT MORE. E.G. THE AND, OR, EX TACTICS
COULD ALL BE BROUGHT TO GETHER.*)

From Stdlib Require Import Arith.

(** Adds H to the context.*)
Ltac addHyp H := generalize H; intro.

(** Inverts and then clears a hypothesis.*)
Ltac invertClear H := inversion H; clear H.

Ltac swapRename A B := let H := fresh in rename A into H; rename B into A; rename H into B.

Ltac introz U := repeat let H := fresh U in intro H.

(*Tries to apply both sides of a disjunction in the hypothesis to the goal,
leaving only the case that didn't fit (if it exists)*)
Ltac appDisj H := destruct H; try apply H.

(** If the hypothesis in question is invertible into exactly one other hypothesis, then
this tactic changes the current hypothesis to the inverted hypothesis. It does this by a
regular inversion, then a clear, then a rename.*)
Ltac invertChange H := let IVC := fresh in inversion H as [IVC];
  clear H; rename IVC into H.

Ltac unwrap_apply2 d := let x := fresh in let y := fresh in
  destruct d as [x y]; apply y.

(*Unwraps something twice and the second time applies a proof contained in the wrapper
at position 2*)
Ltac unwrap2_apply2 d := let x := fresh in destruct d as [x];
  unwrap_apply2 x.

(*Replace x with y and then try and eliminate the subgoal by trying reflexivity.
This leaves only non-trivial equalities as proof obligations. The first part of the
tactic catches existential variables, which shouldn't & don't need to be replaced,
because they'll match anything.*)
Ltac replace_nontriv x y := first [is_evar x |
  (replace x with y; [ |try reflexivity])].

Ltac my_applys_eq1 H :=
  match goal with
  | [ |- ?F ?x1] =>
    match type of H with
    | (?G ?y1) =>
      replace_nontriv x1 y1
    end;
    [apply H |..]
  end.

Ltac my_applys_eq2 H :=
  match goal with
  | [ |- ?F ?x1 ?x2] =>
    match type of H with
    | (?G ?y1 ?y2) =>
      replace_nontriv x1 y1; [replace_nontriv x2 y2 | ..]
    end;
    [apply H |..]
  end.

Ltac my_applys_eq3 H :=
  match goal with
  | [ |- ?F ?x1 ?x2 ?x3] =>
    match type of H with
    | (?G ?y1 ?y2 ?y3) =>
      replace_nontriv x1 y1; [replace_nontriv x2 y2 | ..];
      [replace_nontriv x3 y3 | ..]
    end;
    [apply H |..]
  end.

Ltac my_applys_eq4 H :=
  match goal with
  | [ |- ?F ?x1 ?x2 ?x3 ?x4] =>
    match type of H with
    | (?G ?y1 ?y2 ?y3 ?y4) =>
      replace_nontriv x1 y1; [replace_nontriv x2 y2 | ..];
      [replace_nontriv x3 y3 | ..]; [replace_nontriv x4 y4 | ..]
    end;
    [apply H |..]
  end.

Ltac my_applys_eq5 H :=
  match goal with
  | [ |- ?F ?x1 ?x2 ?x3 ?x4 ?x5] =>
    match type of H with
    | (?G ?y1 ?y2 ?y3 ?y4 ?y5) =>
      replace_nontriv x1 y1; [replace_nontriv x2 y2 | ..];
      [replace_nontriv x3 y3 | ..]; [replace_nontriv x4 y4 | ..];
      [replace_nontriv x5 y5 | ..]
    end;
    [apply H |..]
  end.

Ltac my_applys_eq H := first [my_applys_eq5 H | my_applys_eq4 H |
  my_applys_eq3 H | my_applys_eq2 H | my_applys_eq1 H].

Ltac invertClearAs2 H U V := inversion H as [U V]; clear H.
Ltac invertClearAs3 H U V W := inversion H as [U V W]; clear H.

Ltac elim_intro H H1 H2 := elim H; [intro H1 | intro H2]; clear H.

(*Decompose an or of 3 parts into P1 P2 and P3*)
Ltac decompOr3 P P1 P2 P3 := let H := fresh in elim_intro P P1 H;[ |
  elim_intro H P2 P3].

(*Eliminate an or of n parts into fresh U names.*)
Ltac elimOr2 P U := let U1 := fresh U in elim_intro P U1 U1.
Ltac elimOr3 P U := let H := fresh in let U1 := fresh U in
  elim_intro P U1 H;[ | elimOr2 H U].
Ltac elimOr4 P U := let H := fresh in let U1 := fresh U in
  elim_intro P U1 H;[ | elimOr3 H U].
Ltac elimOr5 P U := let H := fresh in let U1 := fresh U in
  elim_intro P U1 H;[ | elimOr4 H U].

(*Decompose an and of multiple parts into named hypotheses.*)
Ltac decompAnd2 H H1 H2 := elim H; intros H1 H2; clear H.

(*Looks for one conjunction in the hypotheses and flattens the conjuncts into 2
fresh W names.*)
Ltac and_flat_step W :=
  let V1 := fresh W in
  let V2 := fresh W in
  match goal with
  [ H : ?P /\ ?Q |- _] => decompAnd2 H V1 V2
  end.

(*Recursively looks for all conjunctions in the hypothesis and flattens the conjuncts
into W names.*)
Ltac andflat W := repeat and_flat_step W.

(*Decompose an existential H into variables a b c... and proposition Q.*)
Ltac decompEx2 H a b Q := let H1 := fresh in invertClearAs2 H a H1;
  invertClearAs2 H1 b Q.
Ltac decompEx3 H a b c Q := let H1 := fresh in invertClearAs2 H a H1;
  decompEx2 H1 b c Q.
Ltac decompEx4 H a b c d Q := let H1 := fresh in invertClearAs2 H a H1;
  decompEx3 H1 b c d Q.

(*Do the tactic t, then to the first subgoal generated to t again etc.*)
Ltac dofirst2 t := t;[t |..].
Ltac dofirst3 t := t;[dofirst2 t |..].
Ltac dofirst4 t := t;[dofirst3 t |..]. 

(*Decompose and existential conjuction into variable x and conjuncts H1, H2.*)
Ltac decompExAnd H x H1 H2 := let Q := fresh in destruct H as [x Q]; decompAnd2 Q H1 H2.

(** Used to solve the goal which is an inequality between two objects.*)
Ltac neq_inversion := unfold not; let Q := fresh in intro Q; inversion Q.

(**Adds a hypothesis Y to the context and generates a subgoal of unspecified
type such that instantiation of the sub-goal solves it and sets the type
of Y in the original proof context.*)
Ltac eassertArg Y := let P := fresh in
  evar (P:Prop); assert P as Y;[unfold P; clear P
  | unfold P in Y; clear P].

Ltac eassert := let H := fresh in eassertArg H.

Tactic Notation "eassert" "as" ident(Y) := eassertArg Y.

(** Given an equality U : a = b, this tactic first tries to rewrite U
in the goal, then if this does not work rewrites it in a hypothesis.*)
Ltac subst_once U :=
  first [rewrite U |
  match type of U with ?a = ?b =>
   match goal with [U1 : context[a] |- _] =>
   rewrite U in U1
   end
  end].

(** Given a hypothesis a = b, substitutes all occurrences of a with b, then
clears the hypothesis.*)
Ltac subst_all U := match type of U with ?a = ?b =>
  move U at top; repeat subst_once U; clear U end.

(*Looks for one disjunction in the hypotheses and flattens the disjuncts
into 2 fresh W names.*)
Ltac or_flat_step W :=
  let V1 := fresh W in
  let V2 := fresh W in
  match goal with
  [ H : ?P \/ ?Q |- _] => elim_intro H V1 V2
  end.

Ltac or_flat_step_norm := let OR := fresh "OR" in or_flat_step OR.

Ltac or_flat := repeat or_flat_step_norm.

Ltac and_flat := let A := fresh "AND" in andflat A.
  
(** Every time it encounters an existential, decomposes that existential
into a fresh hypothesis and a variable based on "x".*)
Ltac ex_flat := repeat
  let U := fresh in let x := fresh "x" in
  match goal with
  [U1 : context[ex] |- _] =>  invertClearAs2 U1 x U
  end.

(******* Specialised tactics *******)

(**Given a hypothesis H that the length of l = n, for some ACTUAL natural
number n- not a symbolic n or this won't terminate!! This function then uses the dummy
variable LG to turn the hypothesis that the length of l = n to an equation equating l to
an actual list of length n. The name of the equation will be HeqLG (because I can't work
out how to rename it and I'm getting errors with the remember tactic!)*)
Ltac listGen H l := remember l as LG; repeat (destruct LG as [LG|]; invertChange H);
  clear H.

(*Change a network state predicate H to one over a process in a triple of processes, and call
the triple of processes q q0 q1 (if q is fresh). Call the stripped predicate fresh U*)
Ltac netprottrip H U q l h k:=
  let U1 := fresh in let U2 := fresh U in let e := fresh in
  destruct H as [e U1 U2];
  let p := fresh in let U3 := fresh in
  destruct U1 as [p l h k U3];
  let q0 := fresh q in let q1 := fresh q in let q2 := fresh q in let U4 := fresh U in
  destruct U3 as [q0 q1 q2 U4].