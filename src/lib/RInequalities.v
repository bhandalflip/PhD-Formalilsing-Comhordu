From Stdlib Require Export Reals Arith.
From Stdlib Require Import Lra.
Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.Extras.LibTactics.
Open Scope R_scope.

(** Splits the goal into 2 subgoals based on d <= t or t < d*)
Ltac Rleltcases d t U :=  let H := fresh in lets H : Rle_or_lt d t;
                                            let U1 := fresh U in elim_intro H U1 U1.

Lemma not_Rle_lt : forall (r1 r2 : R),
  ~r1 <= r2 -> r2 < r1.
  intros. lra. Qed.

Lemma RltMinusBothSides : forall (r1 r2 : R),
  r2 < r1 -> 0 < (r1 - r2).
  intros. lra. Qed.

(**** Rle ****)

Lemma Rle_plus_r : forall (x y : R),
  0 <= y -> x <= x + y.
  intros. lra. Qed.

Lemma Rle_plus_l : forall (x y : R),
  0 <= y -> x <= y + x.
  intros. lra. Qed.

Lemma RleMinusBothSides : forall (r1 r2 : R),
  r2 <= r1 -> 0 <= (r1 - r2).
  intros. lra. Qed.

Lemma Rmult_le_0_compat : forall r1 r2 : R,
  0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
  intros. nra. Qed.

Lemma Rle_zero_plus : forall r1 r2 : R,
  0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2.
  intros. lra. Qed.

Lemma RlePlusExistsR : forall (r1 r2 : R),
  r1 <= r2 -> exists r3, r2 = r1 + r3 /\ 0 <= r3.
  intros. exists (r2 - r1). split; lra. Qed.

Lemma RlePlusExistsL : forall (r1 r2 : R),
  r1 <= r2 -> exists r3, r2 = r3 + r1 /\ 0 <= r3.
  intros. exists (r2 - r1). split; lra. Qed.

Lemma Rle_or_le : forall (r1 r2 : R), r1 <= r2 \/ r2 <= r1.
  intros. lra. Qed.

Lemma Rplus_le_swap_rr : forall (x y z : R),
  x <= y + z -> x - z <= y.
  intros. lra. Qed.

Lemma Rplus_le_swap_rl : forall (x y z : R),
  x <= y + z -> x - y <= z.
  intros. lra. Qed.

Lemma Rplus_le_swap_lr : forall (x y z : R),
  x + y <= z -> x <= z - y.
  intros. lra. Qed.

Lemma Rplus_le_swap_ll : forall (x y z : R),
  x + y <= z -> y <= z - x.
  intros. lra. Qed.

Lemma Rminus_le_swap_rr : forall (x y z : R),
  x <= y - z -> x + z <= y.
  intros. lra. Qed.

Lemma Rminus_le_swap_lr : forall (x y z : R),
  x - y <= z -> x <= z + y.
  intros. lra. Qed.

Lemma Rplus_le_weaken_lr : forall (x y z : R), x + y <= z -> 0 <= y -> x <= z.
  intros. lra. Qed.

Lemma Rplus_le_weaken_ll : forall (x y z : R), x + y <= z -> 0 <= x -> y <= z.
  intros. lra. Qed.

Lemma Rplus_le_weaken_rr : forall (x y z : R), 0 <= z -> x <= y -> x <= y + z.
  intros. lra. Qed.

Lemma Rminus_le_weaken_lr : forall (x y z : R), 0 <= y -> x <= z -> x - y <= z.
  intros. lra. Qed.

(** Tries to solve an inequality on real numbers.*)
Ltac Rplus_le_tac := 
  match goal with
  | [ H1 : ?r1 <= ?r3, H2 : ?r2 <= ?r4 |- ?r1 + ?r2 <= ?r3 + ?r4] =>
    apply Rplus_le_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 <= ?r3, H2 : ?r2 <= ?r4 |- ?r2 + ?r1 <= ?r3 + ?r4] =>
    rewrite Rplus_comm; apply Rplus_le_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 <= ?r2|- ?r + ?r1 <= ?r + ?r2] =>
    apply Rplus_le_compat_l;apply H1
  | [ H1 : ?r1 <= ?r2|- ?r1 + ?r <= ?r2 + ?r] =>
    apply Rplus_le_compat_r;apply H1
  | [ |- ?r + ?r1 <= ?r + ?r2] =>
    apply Rplus_le_compat_l
  | [ |- ?r1 + ?r <= ?r2 + ?r] =>
    apply Rplus_le_compat_r
  | [ H : ?r1 + ?r <= ?r2 + ?r |- ?r1 <= ?r2] =>
    apply Rplus_le_reg_l in H; assumption
  | [ H : ?r + ?r1 <= ?r + ?r2 |- ?r1 <= ?r2] =>
    apply Rplus_le_reg_r in H; assumption
  | [ H : ?x <= ?y + ?z |- ?x - ?z <= ?y] =>
    apply Rplus_le_swap_rr; assumption
  | [ H : ?x + ?y <= ?z |- ?y <= ?z - ?x] =>
    apply Rplus_le_swap_ll; assumption
  | [ H : ?x + ?y <= ?z |- ?x <= ?z - ?y] =>
    apply Rplus_le_swap_lr; assumption
  | [ H : ?x <= ?y + ?z |- ?x - ?y <= ?z] =>
    apply Rplus_le_swap_rl; assumption
  | [ |- ?r1 <= ?r1 + _] => apply Rle_plus_r
  | [ |- ?r1 <= _ + ?r1] => apply Rle_plus_l
  | [ H : ?x + ?y <= ?z |- ?x <= ?z] =>
    eapply Rplus_le_weaken_lr; apply H
  | [ H : ?x + ?y <= ?z |- ?y <= ?z] =>
    eapply Rplus_le_weaken_ll; apply H
  end.


(**** Rlt ****)

Lemma Rlt_plus_r : forall (x y : R),
  0 < y -> x < x + y.
  intros. lra. Qed.

Lemma Rlt_plus_l : forall (x y : R),
  0 < y -> x < y + x.
  intros. lra. Qed.

Lemma Rlt_zero_plus : forall r1 r2 : R,
  0 < r1 -> 0 < r2 -> 0 < r1 + r2.
  intros. lra. Qed.

Lemma RltPlusExistsR : forall (r1 r2 : R),
  r1 < r2 -> exists r3, r2 = r1 + r3 /\ 0 < r3.
  intros. exists (r2 - r1). split; lra. Qed.

Lemma RltPlusExistsL : forall (r1 r2 : R),
  r1 < r2 -> exists r3, r2 = r3 + r1 /\ 0 < r3.
  intros. exists (r2 - r1). split; lra. Qed.

Lemma Rplus_lt_swap_rl : forall (x y z : R),
  x < y + z -> x - y < z.
  intros. lra. Qed.

Lemma Rplus_lt_swap_rr : forall (x y z : R),
  x < y + z -> x - z < y.
  intros. lra. Qed.

Lemma Rplus_lt_swap_ll : forall (x y z : R),
  x + y < z -> y < z - x.
  intros. lra. Qed.  

Lemma Rplus_lt_swap_lr : forall (x y z : R),
  x + y < z -> x < z - y.
  intros. lra. Qed.

Lemma Rplus_lt_reg_l: forall r r1 r2 : R, r1 + r < r2 + r -> r1 < r2.
  intros. lra. Qed.

Lemma Rplus_lt_reg_r: forall r r1 r2 : R, r + r1 < r + r2 -> r1 < r2.
  intros. lra. Qed.

Lemma Rplus_lt_weaken_lr : forall (x y z : R), x + y < z -> 0 <= y -> x < z.
  intros. lra. Qed.

Lemma Rplus_lt_weaken_ll : forall (x y z : R), x + y < z -> 0 <= x -> y < z.
  intros. lra. Qed.

Lemma Rplus_lt_weaken_rr : forall (x y z : R), 0 <= z -> x < y -> x < y + z.
  intros. lra. Qed.

Lemma Rplus_lt_weaken_rl : forall (x y z : R), 0 <= y -> x < z -> x < y + z.
  intros. lra. Qed.

(** Tries to solve an inequality on real numbers.*) 
Ltac Rplus_lt_tac := 
  match goal with
  | [ H1 : ?r1 < ?r3, H2 : ?r2 < ?r4 |- ?r1 + ?r2 < ?r3 + ?r4] =>
    apply Rplus_lt_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 <= ?r3, H2 : ?r2 < ?r4 |- ?r1 + ?r2 < ?r3 + ?r4] =>
    apply Rplus_le_lt_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 < ?r3, H2 : ?r2 <= ?r4 |- ?r1 + ?r2 < ?r3 + ?r4] =>
    apply Rplus_lt_le_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 < ?r3, H2 : ?r2 < ?r4 |- ?r2 + ?r1 < ?r3 + ?r4] =>
    rewrite Rplus_comm; apply Rplus_lt_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 < ?r2|- ?r + ?r1 < ?r + ?r2] =>
    apply Rplus_lt_compat_l;apply H1
  | [ H1 : ?r1 < ?r2|- ?r1 + ?r < ?r2 + ?r] =>
    apply Rplus_lt_compat_r;apply H1
  | [ H : ?r1 + ?r < ?r2 + ?r |- ?r1 < ?r2] =>
    apply Rplus_lt_reg_l in H; assumption
  | [ H : ?r + ?r1 < ?r + ?r2 |- ?r1 < ?r2] =>
    apply Rplus_lt_reg_r in H; assumption
  | [ H : ?x < ?y + ?z |- ?x - ?z < ?y] =>
    apply Rplus_lt_swap_rr; assumption
  | [ H : ?x + ?y < ?z |- ?y < ?z - ?x] =>
    apply Rplus_lt_swap_ll; assumption
  | [ H : ?x < ?y + ?z |- ?x - ?y < ?z] =>
    apply Rplus_lt_swap_rl; assumption
  | [ H : ?x + ?y < ?z |- ?x < ?z - ?y] =>
    apply Rplus_lt_swap_lr; assumption
  | [ |- ?r1 < ?r1 + _] => apply Rlt_plus_r
  | [ |- ?r1 < _ + ?r1] => apply Rlt_plus_l
  | [ H : ?x + ?y < ?z |- ?x < ?z] =>
    eapply Rplus_lt_weaken_lr; apply H
  | [ H : ?x + ?y < ?z |- ?y < ?z] =>
    eapply Rplus_lt_weaken_ll; apply H
  end.

(** Takes a hypothesis H of type r1 < r2 and gives a hypothesis U of type
r2 = r1 + d'*)
Ltac Rlttoplus H d' U := let Q1 := fresh in lets Q1 : RltPlusExistsL H;
  let U1 := fresh U in let U2 := fresh U in decompExAnd Q1 d' U1 U2.
