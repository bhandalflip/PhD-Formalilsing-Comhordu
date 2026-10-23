(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** The processes of the Comhordú protocol, and their definitions. These instantiate the
generic software language of SoftwareLanguage.v. ProtocolBridge.v shows that the
definitions meet the conditions that some language results need.*)

Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.SoftwareLanguage.

Section Protocol.
Context {Model : ComhModel}.

(**Names for defining parametrised processes.*)
Inductive ProtocolName := bcWaitN | sleepingN | bcReadyN | dormantN | initN | 
  ovWaitN | ovReadyN | switchBcN | switchCurrN | switchListenN | ovAbortN | 
  tfsStartN | tfsNextN | tfsCurrN | tfsBcN | tfsListenN | listeningN | checkRangeN | 
  rangeBadN | currEqN | badOvlpN | currOKN | nextEqN | abortOvlpN | gotMsgN |
  gotRangeN | currPincCheckN | currCompN | nextPincCheckN | pausedN.

(** Equality is decidable on names.*)
Lemma eqDecProtocolName : eqDec ProtocolName.
Proof.
  unfold eqDec.
  destruct x1, x2; try solve [right; unfold not; intro; inversion H];
  left; reflexivity.
Qed.

#[export] Instance protocolNames : ProcNames := {|
  Name := ProtocolName;
  eqDecName := eqDecProtocolName |}.

(** A name applied to the empty list is a process term, which can just be
specified using the name.*)
Coercion liftNameProc (n : ProtocolName) : ProcTerm := n $([])$.

(** Aliases for the protocol's variables, each with its type: the modes m, m' and m'',
the positions l and l', the times t, t', x and y, and the range r. An input binds a
variable only to a value of its type.*)
Definition vM := (var vtMode 0).
Definition vM' := (var vtMode 2).
Definition vM'' := (var vtMode 3).
Definition vL := (var vtPosition 4).
Definition vL' := (var vtPosition 5).
Definition vT := (var vtTime 6).
Definition vT' := (var vtTime 7).
Definition vR := (var vtDistance 8).
Definition vX := (var vtTime 9).
Definition vY := (var vtTime 10).



(******************Broadcast Process*******************)

Definition bcWait (m x : Exp) := chanTrans? sleepingN $+$ $<x>$chanPos$<vL>$? bcReadyN $([m, eVar vL])$ $+$ chanWake$<vM>$? bcWaitN $([eVar vM, liftTimeExp zeroTime])$.

Definition sleeping := chanWake$<vM>$? bcWaitN $([eVar vM, liftTimeExp zeroTime])$ $+$ chanTrans? sleepingN.

Definition bcReady (m l : Exp) := chanOutProc$<[m, l]>$!bcWaitN $([m, (ePeriod m)])$.

(******************Overlap Process*******************)

Definition dormant := chanMNextRead$<vM'>$? initN $(eVar vM')$ $+$ chanAbort? dormantN $+$ chanBad? tfsStartN.

Definition init (m' : Exp) := chanMCurrRead$<vM>$? ovWaitN $([m', (eAdd (eWaitTime vM m') (ePeriod m')), liftTimeExp zeroTime])$.

Definition ovWait (m' t x y : Exp) := chanAbort? ovAbortN $+$ chanBad? tfsStartN $+$ $<y>$chanPos$<vL>$? ovReadyN $([m', t, eVar vL])$ $+$ $<x>$chanPause!switchBcN $(m')$.

Definition ovReady (m' t l : Exp) := chanOutProc$<[m', l]>$!ovWaitN $([m', (eSubtract t (ePeriod m')), (ePeriod m')])$.

Definition switchBc (m' : Exp) := chanWake$<m'>$!switchCurrN.

Definition switchCurr := chanMCurrWrite!switchListenN.

Definition switchListen := chanUnpause!dormantN.

Definition tfsStart := chanMCurrRead$<vM>$? tfsNextN $(eVar vM)$.

Definition tfsNext (m : Exp) := chanMNextWrite$<eFailSafeSucc m>$!tfsCurrN $+$ chanMStableWrite!tfsNextN $(m)$.

Definition tfsCurr := chanAbort? tfsCurrN $+$ chanBad? tfsCurrN $+$ chanMCurrWrite!tfsBcN.

Definition tfsBc := chanTrans!tfsListenN.

Definition tfsListen := chanAbort? tfsListenN $+$ chanBad? tfsListenN $+$ chanUnpause!dormantN.

Definition ovAbort := chanMStableWrite!dormantN.

(******************Listener Process*******************)

(** Notifications arrive as [r, m'', l'], so the listener inputs all three fields and
ignores the position. The thesis inputs only [r, m''] here (p.122), which can never
match a notification: see doc/thesis/thesis-corrections.md.*)
Definition listening := chanAN$<[vR, vM'', vL']>$? checkRangeN $([eVar vM'', eVar vR])$ $+$ chanInProc$<[vM'', vL']>$? gotMsgN $([eVar vM'', eVar vL'])$ $+$ chanPause? pausedN $+$ chanUnpause? listeningN.

(** States for handling notification *)

Definition checkRange (m'' r : Exp) := (bSufficient m'' r $> listeningN) $+$ !~(bSufficient (m'') (r)) $> rangeBadN $(m'')$.

Definition rangeBad (m'' : Exp) := chanMCurrRead$<vM>$? currEqN $([eVar vM, m''])$.

Definition currEq (m m'' : Exp) := (m =b= m'') $> badOvlpN $+$ !~(m =b= m'') $> currOKN $(m'')$.

Definition badOvlp := chanBad!listeningN.

Definition currOK (m'' : Exp) := chanMStableRead? listeningN $+$ chanMNextRead$<vM'>$? nextEqN $([eVar vM', m''])$.

Definition nextEq (m' m'' : Exp) := (m' =b= m'') $> abortOvlpN $+$ !~(m' =b= m'') $> listeningN.

Definition abortOvlp := chanAbort!listeningN.

(** States for handling messages *)

Definition gotMsg (m'' l' : Exp) := chanPos$<vL>$? gotRangeN $([m'', (|vL , l'| (-) speedMax (.) msgLatency)])$.

Definition gotRange (m'' r : Exp) := chanMCurrRead$<vM>$? currPincCheckN $([eVar vM, m'', r])$.

Definition currPincCheck (m m'' r  : Exp) := !~bPossInc m m'' r $> currCompN $([m'', r])$ $+$ bPossInc m m'' r $> badOvlpN.

Definition currComp (m'' r : Exp) := chanMStableRead? listeningN $+$ chanMNextRead$<vM'>$? nextPincCheckN $([eVar vM', m'', r])$.

Definition nextPincCheck (m' m'' r : Exp) :=  !~bPossInc m' m'' r $> listeningN $+$ bPossInc m' m'' r $> abortOvlpN.

Definition paused := chanUnpause? listeningN.


(**The definitions of the protocol's processes. The meaning of protocolDef n = (xs, p) is that
n applied to xs is defined to be p.*)
Definition protocolDef (n : ProtocolName) : (list Var * ProcTerm) :=
  match n with
  | bcWaitN => ([vM, vX], bcWait (eVar vM) (eVar vX))
  | sleepingN => ([], sleeping)
  | bcReadyN => ([vM,  vL ], bcReady (eVar vM)  (eVar vL) )
  | dormantN => ([], dormant)
  | initN => ([vM'], init (eVar vM'))
  (*Only case of any interest. Doubling up on vT in the
    parameter passing. Only process that "passes on" the time parameter.*)
  | ovWaitN => ([vM', vT, vY], ovWait (eVar vM') (eVar vT) (eVar vT) (eVar vY))
  | ovReadyN => ([vM', vT,  vL], ovReady (eVar vM') (eVar vT) (eVar vL))
  | switchBcN => ([vM'], switchBc (eVar vM'))
  | switchCurrN => ([], switchCurr)
  | switchListenN => ([], switchListen)
  | ovAbortN => ([], ovAbort)
  | tfsStartN => ([], tfsStart)
  | tfsNextN => ([vM], tfsNext (eVar vM))
  | tfsCurrN => ([], tfsCurr)
  | tfsBcN => ([], tfsBc)
  | tfsListenN => ([], tfsListen)
  | listeningN => ([], listening)
  | checkRangeN => ([vM'', vR], checkRange (eVar vM'') (eVar vR))
  | rangeBadN => ([vM''], rangeBad (eVar vM''))
  | currEqN => ([vM, vM''], currEq (eVar vM) (eVar vM''))
  | badOvlpN => ([], badOvlp)
  | currOKN => ([vM''], currOK (eVar vM''))
  | nextEqN => ([vM', vM''], nextEq (eVar vM') (eVar vM''))
  | abortOvlpN => ([], abortOvlp)
  | gotMsgN => ([vM'',  vL'], gotMsg (eVar vM'') (eVar vL'))
  | gotRangeN => ([vM'', vR], gotRange (eVar vM'') (eVar vR))
  | currPincCheckN => ([vM, vM'', vR], currPincCheck (eVar vM) (eVar vM'') (eVar vR))
  | currCompN => ([vM'', vR], currComp (eVar vM'') (eVar vR))
  | nextPincCheckN => ([vM', vM'', vR], nextPincCheck (eVar vM') (eVar vM'') (eVar vR))
  | pausedN => ([], paused)
  end.

#[export] Instance protocolDefs : ProcDefs := {| def := protocolDef |}.

(** The protocol process is the parallel composition of the three processes below.
Notice that we could have defined this process via the def relation. However,
the def relation is only necessary for recursive references, of which there are
none here i.e. procProtocol is not on the right hand side of any of the def
equations. Hence there is no need to use the def relation, which in any case would
have made for more cumbersome developments later on.*)
Definition procProtocol := sleeping $||$ dormant $||$ listening.

End Protocol.
