# Workstream: Non-triviality

**STUB - FULL WORKSTREAM PLAN TBD**

| | |
|---|---|
| **Started** | 2026-10-22 |
| **Status** | 🧑 Stub: not started |
| **Goal** | Decide whether to prove that `safety` isn't trivially true, and if so, prove it. |

**Legend:** 🤖 Agent · 🧑 Human-in-the-loop · ✅ / `[x]` done · `[ ]` to do

## Plan

- [ ] 🧑 **1. Analyse.** `safety` would say little if networks were safe whatever software their entities run. The [2015 plan](../archive/2015-05-08-coq-project-plan.pdf) lists a proof that, without the protocol, an unsafe state is reachable as a future extension (§5), since it would show that the protocol is needed. `safety` would also say little if the protocol never let an entity leave a fail-safe mode, because a fail-safe mode needs no distance from any other. Analyse both, and plan the steps that prove what is worth proving.
  - The language takes the process that every entity starts from as a parameter, so the first proof can choose any process.
  - `concrete_model_nondegenerate` in [`src/model/ModelConsistency.v`](../../src/model/ModelConsistency.v) gives a model with a mode that isn't fail-safe and needs a positive distance from itself.

## Final phase

- [ ] 🤖 **Delete this workstream** once every other step is ticked or dropped, after moving anything that must outlive it, as [`AGENTS.md`](AGENTS.md) says.

## Log

- **2026-10-22:** Started as a stub, from a step of the Rocq upgrade and proof completion workstream. The check that the protocol lets an entity leave a fail-safe mode is new.
