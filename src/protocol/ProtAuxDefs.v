(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)


(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtocolBridge.

(********************** Single ProcTerm State Predicates **********************)

(******** Simple ********)

(*Broadcast*)

Section ProtAuxDefs.
Context {Model : ComhModel}.

Definition bcWaitState (m : Mode) (x : Time) (p : ProcTerm) : Prop := 
    p ~p~ (bcWait m x).

Definition sleepingState (p : ProcTerm) : Prop :=
  p ~p~ sleeping.

Definition bcReadyState (m : Mode) (l : Position) (p : ProcTerm) : Prop :=
  p ~p~ (bcReady m l).

(*Overlap*)

Definition dormantState (p : ProcTerm) : Prop :=
  p ~p~ dormant.

Definition ovWaitState (m : Mode) (t x y: Time) (p : ProcTerm) : Prop :=
  p ~p~ ovWait m t x y.

Definition ovReadyState (m : Mode) (t : Time) (l : Position) (p : ProcTerm) : Prop :=
  p ~p~ ovReady m t l.

(** ovWait and ovReady with their timers as expressions. A timer is computed from the modes
read on mNext and mCurr, and the wait time is defined only when the one mode can change to
the other, so a reachable overlap component may hold an ill-formed timer; see the component
shapes in ProtAuxResults.v.*)
Definition ovWaitStateExp (m : Mode) (t x y : Exp) (p : ProcTerm) : Prop :=
  p ~p~ ovWait m t x y.

Definition ovReadyStateExp (m : Mode) (t : Exp) (l : Position) (p : ProcTerm) : Prop :=
  p ~p~ ovReady m t l.

Definition switchBcState (m : Mode) (p : ProcTerm) : Prop :=
  p ~p~ switchBc m.

Definition switchCurrState (p : ProcTerm) : Prop :=
  p ~p~ switchCurr.

Definition switchListenState (p : ProcTerm) : Prop :=
  p ~p~ switchListen.

Definition tfsStartState (p : ProcTerm) : Prop := 
  p ~p~ tfsStart.

Definition tfsNextState (m : Mode) (p : ProcTerm) : Prop :=
  p ~p~ tfsNext m.
 
Definition tfsCurrState (p : ProcTerm) : Prop := 
  p ~p~ tfsCurr.

Definition tfsBcState (p : ProcTerm) : Prop := 
  p ~p~ tfsBc.

Definition tfsListenState (p : ProcTerm) : Prop := 
  p ~p~ tfsListen.

Definition initState (m : Mode) (p : ProcTerm) : Prop := 
  p ~p~ init m.

Definition ovAbortState (p : ProcTerm) : Prop := 
  p ~p~ ovAbort.

(*Listening*)

(*Note that many of the constructors for listeningState actually take a state
that "evaluates" to listeningState so to speak i.e. it is a conditional branch
whose condition is true and whose then branch is the listeningState.*)
Definition listeningState (p : ProcTerm) : Prop :=
  p ~p~ listening.

Definition rangeBadState (m : Mode) (p : ProcTerm) : Prop :=
  p ~p~ rangeBad m.

Definition currOKState (m' : Mode) (p : ProcTerm) : Prop :=
  p ~p~ currOK m'.
  
Definition abortOvlpState (p : ProcTerm) : Prop :=
  p ~p~ abortOvlp.
 
Definition badOvlpState (p : ProcTerm) : Prop :=
  p ~p~ badOvlp.

Definition currCompState (m : Mode) (r : Distance) (p : ProcTerm) : Prop :=
  p ~p~ currComp m r.

Definition pausedState (p : ProcTerm) : Prop := 
  p ~p~ paused.

Definition gotMsgState (m : Mode) (l : Position) (p : ProcTerm) : Prop :=
  p ~p~ gotMsg m l.

Definition gotRangeState (m : Mode) (r : Distance) (p : ProcTerm) : Prop :=
  p ~p~ gotRange m r.

Definition currEqState (m m' : Mode) (p : ProcTerm) : Prop := 
  p ~p~ currEq m m'.

Definition nextEqState (m m' : Mode) (p : ProcTerm) : Prop := 
  p ~p~ nextEq m m'.

Definition currPincCheckState (m m' : Mode) (d : Distance) (p : ProcTerm) : Prop := 
  p ~p~ currPincCheck m m' d.
	
Definition nextPincCheckState (m m' : Mode) (d : Distance) (p : ProcTerm) : Prop := 
  p ~p~ nextPincCheck m m' d.

(******** Compound ********)

(*Broadcast*)

(** The states of a component are the processes reachable from its initial process. Each
one is bisimilar to one of the named states above, with the parameters the component has
received so far; ProtAuxResults.v proves that characterisation.*)
Definition broadcastState : ProcTerm -> Prop := reachableFrom sleeping.

(*Overlap*)

Definition overlapState : ProcTerm -> Prop := reachableFrom dormant.

Inductive nextSinceState (p : ProcTerm) : Prop :=
  | nexsOvwSt (m : Mode) (t x y : Time) : ovWaitState m t x y p -> nextSinceState p
  | nexsOvrSt (m : Mode) (t : Time) (l : Position) : ovReadyState m t l p -> nextSinceState p
  | nexsSbcSt (m : Mode) : switchBcState m p -> nextSinceState p
  | nexsScSt (m : Mode) : switchCurrState p -> nextSinceState p.

Inductive tfsState (p : ProcTerm) : Prop :=
  | tfsStaSt : tfsStartState p -> tfsState p
  | tfsNexSt (m : Mode) : tfsNextState m p -> tfsState p
  | tfsCurSt : tfsCurrState p -> tfsState p
  | tfsBcSt : tfsBcState p -> tfsState p
  | tfsLisSt : tfsListenState p -> tfsState p.

Inductive switchState (p : ProcTerm) : Prop :=
  | switBcSt (m : Mode) : switchBcState m p -> switchState p
  | switCurSt : switchCurrState p -> switchState p
  | switLisSt : switchListenState p -> switchState p.

(*Listening*)

Definition listenerState : ProcTerm -> Prop := reachableFrom listening.

  

(********************** Protocol Lift State Predicates **********************)

(******** Lifting Functions ********)

Inductive liftBroadcast (X : ProcTerm -> Prop) : ProcTerm -> Prop :=
  | lftbc (p p2 p3 : ProcTerm) : X p -> liftBroadcast X (p $||$ p2 $||$ p3) .

Inductive liftOverlap (X : ProcTerm -> Prop) : ProcTerm -> Prop :=
  | lftOv (p1 p p3 : ProcTerm) : X p -> liftOverlap X (p1 $||$ p $||$ p3) .

Inductive liftListen (X : ProcTerm -> Prop) : ProcTerm -> Prop :=
  | lftlst (p1 p2 p : ProcTerm) : X p -> liftListen X (p1 $||$ p2 $||$ p) .

(******** Simple ********)

(*Broadcast*)

Definition bcWaitStateProt m x := liftBroadcast (bcWaitState m x).
Definition bcReadyStateProt m l := liftBroadcast (bcReadyState m l).

(*Overlap*)

Definition dormantStateProt := liftOverlap dormantState.
Definition ovWaitStateProt m' t x y := liftOverlap (ovWaitState m' t x y).
Definition tfsListenStateProt := liftOverlap tfsListenState.
Definition tfsBcStateProt := liftOverlap tfsBcState.
Definition tfsCurrStateProt := liftOverlap tfsCurrState.
Definition ovAbortStateProt := liftOverlap ovAbortState.
Definition switchBcStateProt m := liftOverlap (switchBcState m).
Definition tfsNextStateProt m := liftOverlap (tfsNextState m).
Definition tfsStartStateProt := liftOverlap tfsStartState.
Definition initStateProt m := liftOverlap (initState m).
Definition ovReadyStateProt m t l := liftOverlap (ovReadyState m t l).
Definition ovReadyStateExpProt m t l := liftOverlap (ovReadyStateExp m t l).
Definition switchCurrStateProt := liftOverlap switchCurrState.
Definition switchListenStateProt := liftOverlap switchListenState.

(*Listening*)

Definition listeningStateProt := liftListen listeningState.
Definition currCompStateProt m'' r := liftListen (currCompState m'' r).
Definition abortOvlpStateProt := liftListen abortOvlpState.
Definition badOvlpStateProt := liftListen badOvlpState.
Definition pausedStateProt := liftListen pausedState.
Definition gotMsgStateProt m l := liftListen (gotMsgState m l).
Definition gotRangeStateProt m r := liftListen (gotRangeState m r).
Definition rangeBadStateProt m := liftListen (rangeBadState m).
Definition currOKStateProt m := liftListen (currOKState m).
Definition currEqStateProt m m'' := liftListen (currEqState m m'').
Definition nextEqStateProt m m' := liftListen (nextEqState m m').
Definition currPincCheckStateProt m m'' r := liftListen (currPincCheckState m m'' r).

(******** Compound ********)

(*Broadcast*)

Definition broadcastStateProt :=  liftBroadcast broadcastState.

(*Overlap*)

Definition overlapStateProt := liftOverlap overlapState.
Definition nextSinceStateProt := liftOverlap nextSinceState.
Definition tfsStateProt := liftOverlap tfsState.
Definition switchStateProt := liftOverlap switchState.

(*Listening*)

Definition listenerStateProt := liftListen listenerState.

(********************** Other **********************)

Inductive protocolState : ProcTerm -> Prop :=
  | protState (p1 p2 p3 : ProcTerm) :
    broadcastState p1 -> overlapState p2 -> listenerState p3 ->
    protocolState (p1 $||$ p2 $||$ p3).

(** Reachability from the protocol process. Any process that is reachable from the
  protocol process via a finite number of steps as per the semantics satisfies this relation.*)
Inductive reachableProt : ProcTerm -> Prop :=
  | reachprBase : reachableProt procProtocol
  | reachprDisc (p p' : ProcTerm) (a : DiscAct) : reachableProt p ->
  p -PA- a -PA> p' -> reachableProt p'
  | reachprDel (p p' : ProcTerm) (d : Delay) : reachableProt p ->
  p -PD- d -PD> p' -> reachableProt p'.

End ProtAuxDefs.
