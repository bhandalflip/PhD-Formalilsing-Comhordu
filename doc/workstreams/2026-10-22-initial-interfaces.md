# Workstream: Initial interfaces

**STUB - FULL WORKSTREAM PLAN TBD**

| | |
|---|---|
| **Started** | 2026-10-22 |
| **Status** | 🧑 Stub: not started |
| **Goal** | Decide whether an entity's interface should start constrained, for example empty, and if so, constrain it. |

**Legend:** 🤖 Agent · 🧑 Human-in-the-loop · ✅ / `[x]` done · `[ ]` to do

## Plan

- [ ] 🧑 **1. Analyse.** `initialEnt` in [`src/lang/EntityLanguage.v`](../../src/lang/EntityLanguage.v) lets an entity start with anything in its interface, and the thesis's Definition 6.1 (p.133) says nothing about the interface either. That is why `incomingNetNotif_del` in [`src/protocol/NetAuxBasics.v`](../../src/protocol/NetAuxBasics.v) holds only for a notification of the shape the listener reads: a range, a mode and a position. Decide whether `initialEnt` should constrain the interface, for example to start empty, and if so, plan the steps.

## Final phase

- [ ] 🤖 **Delete this workstream** once every other step is ticked or dropped, after moving anything that must outlive it, as [`AGENTS.md`](AGENTS.md) says.

## Log

- **2026-10-22:** Started as a stub, from a step of the Rocq upgrade and proof completion workstream.
