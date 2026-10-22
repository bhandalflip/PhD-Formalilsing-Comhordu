(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import List.
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
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.NetAuxBasics.
Require Import ComhCoq.protocol.ProtocolBridge.

Section NetAuxDefs.
Context {Model : ComhModel}.

(*tfs m t i n p says that the entity i in the network n has been transitioning
to a fail safe mode from the mode m for a time of t. Transitioning to fail safe
is a standard definition which takes as a base case a certain state and records
a time of zero. The condition is preserved by future states as long as they belong
to a certain subset of locations (state patterns). Since delay does not alter location,
we do not need this stipulation in the premise of the delay case. Rather, we simply
add the value of the delay to the running total of time so far.*)
Inductive tfs (m : Mode) : Time -> nat -> forall n : Network, reachableProtNet n -> Prop := 
  | tfsBase (i : nat) (n : Network) (p : reachableProtNet n) :
    tfsStartStateNet i n -> currModeNet m i n -> tfs m zeroTime i n p
  | tfsDisc (a : ActDiscNet) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
    tfs m t i n p -> tfsStateNet i n' -> tfs m t i n' (reachNetDisc n n' a p w)
  | tfsDel (d : Delay) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -ND- d -ND> n') :
    tfs m t i n p -> tfs m (t +dt+ d) i n' (reachNetDel n n' d p w).

(*pending i n p is a relation that is set up purely as a precursor to nextSince.
It is needed in order to "normalise" the relationship between the time parameter
of the waiting state and that of nextSince, for initially there is a a corner case
in which there is an extra period m added to the waiting time parameter.
Pending i n only lasts for two states, and then it hands control over to nextSince.
Note we don't include any delay constructors. This is because it should be provable
that a state cannot delay when it is pending.*)
Inductive pending (i : nat) : forall n : Network, reachableProtNet n -> Prop :=
  | pendingBase (a : ActDiscNet) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') (m : Mode) (t x y : Time) :
    initStateNet m i n -> ovWaitStateNet m t x y i n' -> pending i n' (reachNetDisc n n' a p w)
  | pendingWait (a : ActDiscNet) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') (m : Mode) (t x y : Time) :
    pending i n p -> ovWaitStateNet m t x y i n -> ovWaitStateNet m t x y i n' -> pending i n' (reachNetDisc n n' a p w)
  | pendingWaitReady (a : ActDiscNet) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') (m : Mode) (l : Position) (t x y : Time) :
    pending i n p -> ovWaitStateNet m t x y i n -> ovReadyStateNet m t l i n' -> pending i n' (reachNetDisc n n' a p w)    
  | pendingReady (a : ActDiscNet) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') (m : Mode) (l : Position) (t : Time) :
    pending i n p -> ovReadyStateNet m t l i n -> ovReadyStateNet m t l i n' -> pending i n' (reachNetDisc n n' a p w).


(*nextSince m t i n roughly says that entity i in the reachable network
n has initiated a mode transition to m and has been broadcasting mode m
messages since t time units ago. The base case says that if between
states we change from the state "ovReady" to "ovWait", with parameter m,
then we have just begun the mode transition to m, and so our time parameter
t is 0. The discrete inductive case states that when an we have been nextSince
m in a certain network, and in a derivative network, we are still in a
"nextSinceStateNet", then we are still nextSince in the derivative network.
The time parameter has not changed because the action was discrete.
The timed case is similar except that we do update the time by adding the delay to it.
Also, we don't need to assert that we are still in a "nextSinceStateNet" in the
derivative state- we should be able to prove that being in such a state is
preserved by the delay relation. Reachability is implicitly carried forward
from pending, and so does not need explicit mention in these rules. Notice
also in the base case that t' is free with respect to t, allowing for the
time to be updated.*)
Inductive nextSince (m : Mode) : Time -> nat -> forall n : Network, reachableProtNet n -> Prop :=
  | nextSinceBase (a : ActDiscNet) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') (l : Position) (t t' x y : Time) :
    pending i n p -> ovReadyStateNet m t l i n -> ovWaitStateNet m t' x y i n' ->
    nextSince m zeroTime i n' (reachNetDisc n n' a p w)
  | nextSinceDisc (a : ActDiscNet) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
    nextSince m t i n p -> nextSinceStateNet i n' -> nextSince m t i n' (reachNetDisc n n' a p w)
  | nextSinceDel (d : Delay) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -ND- d -ND> n') :
    nextSince m t i n p -> nextSince m (t +dt+ d) i n' (reachNetDel n n' d p w).

(*currSince m t i n roughly says that entity i in the network n has
been broadcasting mode m messages since t time units ago and is now
operating with m as the current mode. In the base case of this relation,
we have that an entity in a network is currSince m t if a predecessor
network had that same entity as nextSince m t, and in the process of
the transition the entity has gone from a switchCurrStateNet to a
swtichListenStateNet. It can be shown that this transition implies
that the mode m must be sent to the mode state, causing a mode switch.
Notice that the time parameter t is passed along from one relation to the next
in the fashion of a bat from one member of a relay team to the next. This is
essential in proving properties of currSince that carry over from nextSince.
The inductive cases are simple, and follow the standard pattern
shared by much of the "history relations" given here. It is worth noting
that there is no need to explicitly enforce reachability here in the base case
because it will follow from the "passing on of the relay bat" from nextSince.*)
Inductive currSince (m : Mode) : Time -> nat -> forall n : Network, reachableProtNet n -> Prop :=
  | currSinceBase (a : ActDiscNet) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
    nextSince m t i n p -> switchCurrStateNet i n -> switchListenStateNet i n' ->
    currSince m t i n' (reachNetDisc n n' a p w)
  | currSinceDisc (a : ActDiscNet) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
    currSince m t i n p -> currModeNet m i n' -> currSince m t i n' (reachNetDisc n n' a p w)
  | currSinceDel (d : Delay) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -ND- d -ND> n') :
    currSince m t i n p -> currSince m (t +dt+ d) i n' (reachNetDel n n' d p w).				 


(*Relation capturing the sending of a message from the software component to the interface component.
The base case is the only case of any interest here. It says that v was sent in this instant
(0 time units ago) by entity i, when the entity at i can transform by its software component
outputting v and its interface component inputting, along the channel outProc.
One thing to note is that sent, like many of these history relations, is preserved by both transitions,
as you would expect, i.e. if a message has been sent at some point, then it remains sent at a later point.
Also, at this later point, the time parameter will not have decreased- though it may have increased.
Sent can be seen as a means of encoding what happened in the past, a way of remembering some of the
history that brought us to this state. The parameter p of type reachableProtNet n remembers the exact history
up to this point. Sent is like a summary of this or a statistic over p.*)				 
Inductive sent (v : list BaseValue) : Time -> nat -> forall n : Network, reachableProtNet n -> Prop :=
  | sentBase (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- anTau -NA> n')
    (q q' : ProcTerm) (l : Position) (h h' : Interface) (k : ModeState) :
    [| q, l, h, k |] @ i .: n -> [| q', l, h', k |] @ i .: n' -> 
    q -PA- (outAct chanOutProc v) -PA> q' -> h -i- (aiIn chanOutProc v) -i> h' ->
    sent v zeroTime i n' (reachNetDisc n n' anTau p w)
  | sentDisc (a : ActDiscNet) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
    sent v t i n p -> sent v t i n' (reachNetDisc n n' a p w)
  | sentDel (d : Delay) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -ND- d -ND> n') :
    sent v t i n p -> sent v (t +dt+ d) i n' (reachNetDel n n' d p w).

(*delivered v r t i n p says that the message v was delivered to the radius r t time units
ago by the entity i in the network n.*)
Inductive delivered (v : Message) : Time -> nat -> forall n : Network, reachableProtNet n -> Prop :=
  | deliveredBase (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- (anOut v i) -NA> n') :
    delivered v zeroTime i n' (reachNetDisc n n' (anOut v i) p w)
  | deliveredDisc (a : ActDiscNet) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
    delivered v t i n p -> delivered v t i n' (reachNetDisc n n' a p w)
  | deliveredDel (d : Delay) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -ND- d -ND> n') :
    delivered v t i n p -> delivered v (t +dt+ d) i n' (reachNetDel n n' d p w).

(*received v t i n p says that the message v was received t time units ago by the entity i in the network n.*)
Inductive received (v : list BaseValue) : Time -> nat -> forall n : Network, reachableProtNet n -> Prop :=
  | receivedBase (a : ActDiscNet) (i : nat) (n n' : Network) (p : reachableProtNet n)
  (w : n -NA- a -NA> n') (e e' : Entity) (l : Position) (r : Distance) :
    e @ i .: n -> e' @ i .: n' -> e -EA- (aeTagIn ([- v, l, r -])) ->> e' ->
    received v zeroTime i n' (reachNetDisc n n' a p w)
  | receivedDisc (a : ActDiscNet) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -NA- a -NA> n') :
    received v t i n p -> received v t i n' (reachNetDisc n n' a p w)
  | receivedDel (d : Delay) (t : Time) (i : nat) (n n' : Network) (p : reachableProtNet n) (w : n -ND- d -ND> n') :
    received v t i n p -> received v (t +dt+ d) i n' (reachNetDel n n' d p w).

(***************************** Path predicates *****************************)


Definition msgBadPathNet := liftEntNet msgBadPathEnt.
Definition notifBadPathNet := liftEntNet notifBadPathEnt.
Definition msgAbortPathNet := liftEntNet msgAbortPathEnt.
Definition notifAbortPathNet := liftEntNet notifAbortPathEnt.

(*LOCAL TIDY*)

(*Tidy these to some common NAR file? Or just leave them here for the moment? I think
I'll leave them. No point creating a new file unless this one gets overbearingly big.
Who cares if this is strictly the "Defs" file.*)
(*Proofs of these are all similar, tactify the following:
>Assert the existence of a mode in derivative
>Assume modes are unequal towards a contradiction
>Use inequality of modes to assert the pre and post states (theorem already- tactic?)
>Show that the paused-state holds (theorems alredy for this?)
>Destruct path predicate to get all the possible state predicates on listener, and in each
case, state_pred_elim_net gets rid of these by contradiction
*)

End NetAuxDefs.

(*-LOCAL TIDY*)
