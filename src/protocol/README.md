# protocol/: the protocol and its safety proof

The Comhordú protocol (thesis chapter 5, p.102), written in the [language](../lang/README.md), and the proof that it is safe (chapter 6, p.130). The top-level theorem is `safety` in [`Main.v`](Main.v):

```coq
Theorem safety (n : Network) : reachableProtNet n -> safe n.
```

The proof builds up level by level, from processes to entities to networks. Every result here serves `safety`, except a few kept for proofs of other properties, such as liveness or that time can always pass: `protocolGuarded` and `delApp` in `ProtocolBridge.v`, and some facts in `ProtAuxResults.v`, `EntAuxResults.v` and `NetAuxBasics.v` about what a component can do next, or where it goes next.

| File | What it holds |
|---|---|
| [`Protocol.v`](Protocol.v) | The protocol's processes and their definitions. |
| [`ProtocolBridge.v`](ProtocolBridge.v) | Proofs that the protocol meets the language's conditions, such as guarded definitions and correct use of its entity's channels, and facts true only of this protocol. |
| [`ProtAuxDefs.v`](ProtAuxDefs.v), [`ProtAuxResults.v`](ProtAuxResults.v) | State predicates over the protocol's processes, and results about them. |
| [`EntAuxDefs.v`](EntAuxDefs.v), [`EntAuxResults.v`](EntAuxResults.v) | The state predicates lifted to entities, path predicates for reasoning about reactions to events, and results about them. |
| [`NetAuxBasics.v`](NetAuxBasics.v) | The protocol's initial and reachable networks, which are the language's at the protocol process; a network step taken to the components of the protocol's triple; and the state predicates lifted to networks. |
| [`NetAuxDefs.v`](NetAuxDefs.v) | The history relations at the heart of the proof. |
| [`NARIncomp.v`](NARIncomp.v), [`NARInsuff.v`](NARInsuff.v), [`NARMisc.v`](NARMisc.v), [`NARMsgPosition.v`](NARMsgPosition.v), [`NARNonFS_currSince.v`](NARNonFS_currSince.v), [`NAROvlpTime.v`](NAROvlpTime.v) | Results about the history relations, each file loosely themed around one key result. |
| [`NARTop.v`](NARTop.v) | Ties the other `NAR` results together. |
| [`Main.v`](Main.v) | The safety proof. |
