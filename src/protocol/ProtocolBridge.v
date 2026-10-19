(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** The bridge between the generic software language and the Comhordú protocol. Some
language results hold only for definitions that meet certain conditions. This file shows
that the protocol's definitions meet them, by giving the instances the language asks for.
It also proves facts about the language that hold for this protocol but not in general.*)

Require Import ComhCoq.lib.Extras.LibTactics.
Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Export ComhCoq.protocol.Protocol.
From Stdlib Require Import Lia.

(******************Guardedness*******************)

(** A rank for each process name. Only the decision states call other processes outside
an input or output prefix, and the processes they call have a lower rank.*)
Definition protocolRank (n : ProtocolName) : nat :=
  match n with
  | checkRangeN | currEqN | nextEqN | currPincCheckN | nextPincCheckN => 1
  | _ => 0
  end.

(** Each definition only calls lower-ranked processes outside a prefix.*)
Lemma protocolRank_unguarded (h h' : Name) :
  In h' (unguardedNames (snd (def h))) -> (protocolRank h' < protocolRank h)%nat.
Proof.
  intro I. destruct h; simpl in I;
    repeat (destruct I as [I | I]; [subst; simpl; lia | ]); contradiction.
Qed.

(** The protocol's definitions are guarded.*)
#[export] Instance protocolGuarded : GuardedDefs := {|
  rank := protocolRank;
  rank_unguarded := protocolRank_unguarded |}.

(******************Protocol-specific language facts*******************)

Open Scope R_scope.

(** A single step of the full automation tactic for "eventually discrete guarded sum" terms.*)
Ltac taeAutoSing := match goal with
  | [ |- timedActEnabled ?P _ ] =>
    match P with
    | _ $< _ >$ ? _  => apply taeIn
    | _ $< _ >$ ! _  => apply taeOut
    | _ $> _  => apply taeThenBranch
    | _ $+$ _  => apply taeSum
    | _ $(_)$  => apply taeAppAuto; simpl
    | $< _ >$ _  => apply taeDel
    end
  end.

(** A tactic that will automatically prove that certain processes are time
action enabled. It does this by repeatedly drilling into the process until it finds
either input or output prefixed terms, at which point the delay proof is simple.
Obviously, this will only work for a certain class of processes that are, let's say
"eventually discrete guarded sums" i.e. if they were put in some sort of normal form,
with all the applications expanded to their definitions, then they would be sums of
input or output prefixed terms.*)
Ltac taeAuto := repeat taeAutoSing.

(** Every application of a name to a vector can progress by a delay. To prove this
we need to use heavy automation tactics rather than step through all 30 names
individually. The automation tactic we use is taeAuto.*)
Theorem delApp : forall (h : Name) (l : list Exp),
  exists d, timedActEnabled (h $(l)$) d.  intros.
  exists (mkDelay onePos). remember (def h) as e.
  symmetry in Heqe. destruct e as [x p]. destruct h;
  (** This next block of code replaces the application of a name to a generic list of
  expressions with the body instantiated with a normalised generic list of expressions.
  By normalisation what is meant here is that the length of the target list matches the
  length of the parameter list in the definition. This is possible due to previous results.*)
  (eapply taeApp; [apply Heqe|]; addHyp (listSubNormal x l); rename X into H;
  invertClear H; invertClear H0; rename x0 into l'; rewrite H1;
  inversion Heqe; rewrite <- H2 in H; listGen H l'; simpl);
  taeAuto. Qed.

(******************Channels*******************)

(** The protocol uses its entity's channels correctly: computing the channels of every prefix
of its processes and of their definitions shows that none goes the wrong way.*)
Lemma protocol_correctChannelUsage : correctChannelUsage procProtocol.
Proof.
  apply correctChannelUsage_prefixes; [ | intro n; destruct n];
    unfold prefixesRightWay; cbn; repeat apply Forall_cons; try apply Forall_nil;
    first [left; reflexivity | right; reflexivity].
Qed.
