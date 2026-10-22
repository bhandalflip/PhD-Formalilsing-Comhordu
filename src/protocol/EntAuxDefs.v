(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)


(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.ProtocolBridge.


(***************************** Lifting *****************************) 
(** The protocol's state predicates, lifted to entities by the language's liftProcEnt.*)

(******** Simple Lifted Predicates ********) 

Section EntAuxDefs.
Context {Model : ComhModel}.

(*Broadcast*)
Definition bcWaitStateEnt (m : Mode) (x : Time) : Entity -> Prop :=
liftProcEnt (bcWaitStateProt m x).
Definition bcReadyStateEnt  (m : Mode) (l : Position) : Entity -> Prop :=
liftProcEnt (bcReadyStateProt m l).

(*Overlap*)
Definition dormantStateEnt : Entity -> Prop :=
liftProcEnt dormantStateProt.
Definition tfsStartStateEnt : Entity -> Prop :=
liftProcEnt tfsStartStateProt.
Definition initStateEnt (m : Mode) : Entity -> Prop :=
liftProcEnt (initStateProt m).
Definition ovReadyStateEnt (m : Mode) (t : Time) (l : Position) : Entity -> Prop :=
liftProcEnt (ovReadyStateProt m t l).
Definition ovReadyStateExpEnt (m : Mode) (t : Exp) (l : Position) : Entity -> Prop :=
liftProcEnt (ovReadyStateExpProt m t l).
Definition switchCurrStateEnt : Entity -> Prop :=
liftProcEnt switchCurrStateProt.
Definition switchListenStateEnt : Entity -> Prop :=
liftProcEnt switchListenStateProt.
Definition tfsListenStateEnt := liftProcEnt tfsListenStateProt.
Definition ovAbortStateEnt := liftProcEnt ovAbortStateProt.
Definition tfsBcStateEnt := liftProcEnt tfsBcStateProt.
Definition switchBcStateEnt m := liftProcEnt (switchBcStateProt m).
Definition ovWaitStateEnt (m : Mode) (t x y : Time) : Entity -> Prop :=
liftProcEnt (ovWaitStateProt m t x y).
Definition tfsCurrStateEnt := liftProcEnt tfsCurrStateProt.
Definition tfsNextStateEnt m := liftProcEnt (tfsNextStateProt m).

(*Listener*)
Definition listeningStateEnt : Entity -> Prop :=
liftProcEnt listeningStateProt.
Definition currCompStateEnt (m : Mode) (r : Distance) : Entity -> Prop :=
liftProcEnt (currCompStateProt m r).
Definition pausedStateEnt := liftProcEnt pausedStateProt.
Definition abortOvlpStateEnt := liftProcEnt abortOvlpStateProt.
Definition badOvlpStateEnt := liftProcEnt badOvlpStateProt.
Definition nextEqStateEnt m m' := liftProcEnt (nextEqStateProt m m').
Definition currEqStateEnt m m'' := liftProcEnt (currEqStateProt m m'').
Definition currOKStateEnt m'' := liftProcEnt (currOKStateProt m'').
Definition gotMsgStateEnt m l := liftProcEnt (gotMsgStateProt m l).
Definition gotRangeStateEnt m r := liftProcEnt (gotRangeStateProt m r).
Definition currPincCheckStateEnt m m'' r := liftProcEnt (currPincCheckStateProt m m'' r).
Definition rangeBadStateEnt m := liftProcEnt (rangeBadStateProt m).


(******** Compound Lifted Predicates ********) 

(*Broadcast*)

Definition broadcastStateEnt := liftProcEnt broadcastStateProt.

(*Overlap*)
Definition overlapStateEnt : Entity -> Prop :=
liftProcEnt overlapStateProt.
Definition nextSinceStateEnt : Entity -> Prop :=
liftProcEnt nextSinceStateProt.
Definition tfsStateEnt : Entity -> Prop :=
liftProcEnt tfsStateProt.
Definition switchStateEnt : Entity -> Prop :=
liftProcEnt switchStateProt.

(*Listener*)
Definition listenerStateEnt : Entity -> Prop :=
liftProcEnt listenerStateProt.


(***************************** Path predicates *****************************)


Inductive msgBadPathEnt : Entity -> Prop :=
  | mbpMsg p l h k m'' m l' : gotMsgStateProt m'' l' p -> currModeMState k = m -> 
    possiblyIncompatible m m'' (dist2d l l' -nn- speedMax *nn* msgLatency)
    -> msgBadPathEnt ([| p, l, h, k|])
  | mbpRng p l h k m'' m r : gotRangeStateProt m'' r p -> currModeMState k = m ->
    possiblyIncompatible m m'' r -> msgBadPathEnt ([|p, l, h, k|])
  | mbpBad p l h k : badOvlpStateProt p ->  msgBadPathEnt ([|p, l, h, k|]).

Inductive notifBadPathEnt : Entity -> Prop :=
  | nbpRng p l h k m : rangeBadStateProt m p -> currModeMState k = m ->
    notifBadPathEnt ([|p, l, h, k|])
  | nbpBad p l h k : badOvlpStateProt p -> notifBadPathEnt ([|p, l, h, k|]).

Inductive msgAbortPathEnt : Entity -> Prop :=
  | mapMsg p l h k m'' m m' l' :
    let r' := dist2d l l' -nn- speedMax *nn* msgLatency in
    gotMsgStateProt m'' l' p -> currModeMState k = m ->
    ~possiblyIncompatible m m'' r' -> 
    nextModeMState k = Some m' ->
    possiblyIncompatible m' m'' r' ->
    msgAbortPathEnt ([|p, l, h, k|])
  | mapGrng p l h k m'' m m' r : gotRangeStateProt m'' r p -> currModeMState k = m ->
   ~possiblyIncompatible m m'' r -> nextModeMState k = Some m' ->
    possiblyIncompatible m' m'' r -> msgAbortPathEnt ([|p, l, h, k|])
  | mapCuco p l h k m'' m' r : currCompStateProt m'' r p -> nextModeMState k = Some m' ->
    possiblyIncompatible m' m'' r -> msgAbortPathEnt ([|p, l, h, k|])
  | mapAbort p l h k : abortOvlpStateProt p -> msgAbortPathEnt ([|p, l, h, k|]).

Inductive notifAbortPathEnt : Entity -> Prop :=
  | napRng p l h k m m' : rangeBadStateProt m' p -> currModeMState k = m -> m <> m' ->
    nextModeMState k = Some m' -> notifAbortPathEnt ([|p, l, h, k|])
  | napCuok p l h k m' : currOKStateProt m' p -> nextModeMState k = Some m' ->
    notifAbortPathEnt ([|p, l, h, k|])
  | napAbort p l h k : abortOvlpStateProt p -> notifAbortPathEnt ([|p, l, h, k|]).

End EntAuxDefs.

(***************************** Misc *****************************)

(** Reachable entities for the protocol are the language's, with the protocol process as the
seed, as reachableProtNet is for networks. They are closed under every entity action, the
half actions included: a half action only means a message from an entity outside the
network, which the protocol has to cope with anyway.*)
Notation reachableProtEnt := (reachableEnt procProtocol).
