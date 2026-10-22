# model/: the Comhordú model

The revised Comhordú model of the thesis (§3.3, p.41), stated as a class whose fields any use of the protocol must supply. They include the modes and which of them are fail-safe, how one mode may change to another, the message latency, the maximum speed, and the minimum distance at which two modes are compatible. The model builds only on [`lib/`](../lib/README.md).

| File | What it holds |
|---|---|
| [`ComhBasics.v`](ComhBasics.v) | The model, as the class `ComhModel`, and what is defined from it, such as when a broadcast's coverage is sufficient for a mode. |
| [`ModelConsistency.v`](ModelConsistency.v) | A concrete model, built without axioms and not degenerate, which shows that the model's assumptions are consistent. |
