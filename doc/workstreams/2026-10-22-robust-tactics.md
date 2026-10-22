# Workstream: Robust tactics

**STUB - FULL WORKSTREAM PLAN TBD**

| | |
|---|---|
| **Started** | 2026-10-22 |
| **Status** | 🧑 Stub: not started |
| **Goal** | Proofs use only robust tactics, so they don't break for reasons unrelated to what they prove. |

**Legend:** 🤖 Agent · 🧑 Human-in-the-loop · ✅ / `[x]` done · `[ ]` to do

## Plan

- [ ] 🧑 **1. Analyse.** Find what makes today's proofs fragile, and plan the steps that fix it:
  - Replace the project's own tactics with proved results wherever a lemma can do the same job.
  - Stop using LibTactics, Arthur Charguéraud's tactic library, vendored as [`src/lib/Extras/LibTactics.v`](../../src/lib/Extras/LibTactics.v). 24 of the other 29 files import it.
  - Make the tactics that remain robust. For example, a proof should not depend on the names Rocq makes up for new hypotheses, such as `H12`, or on the order it creates them in.

## Final phase

- [ ] 🤖 **Delete this workstream** once every other step is ticked or dropped, after moving anything that must outlive it, as [`AGENTS.md`](AGENTS.md) says.

## Log

- **2026-10-22:** Started as a stub.
