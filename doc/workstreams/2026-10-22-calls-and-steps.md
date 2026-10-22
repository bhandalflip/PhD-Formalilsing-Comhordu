# Workstream: Calls and steps

**STUB - FULL WORKSTREAM PLAN TBD**

| | |
|---|---|
| **Started** | 2026-10-22 |
| **Status** | 🧑 Stub: not started |
| **Goal** | Decide whether to study when reachability by calls and reachability by steps and delays agree, and if so, study it. |

**Legend:** 🤖 Agent · 🧑 Human-in-the-loop · ✅ / `[x]` done · `[ ]` to do

## Plan

- [ ] 🧑 **1. Analyse.** `reachableFrom_nameCallReachable` in [`src/lang/SoftwareLanguage.v`](../../src/lang/SoftwareLanguage.v) shows that every name a process reaches by steps and delays, it also reaches by calls ([#17](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/17)). The converse fails, since a process can get stuck before it unfolds an application. Decide whether to study when the two agree, and if so, plan the steps.

## Final phase

- [ ] 🤖 **Delete this workstream** once every other step is ticked or dropped, after moving anything that must outlive it, as [`AGENTS.md`](AGENTS.md) says.

## Log

- **2026-10-22:** Started as a stub, from a step of the Rocq upgrade and proof completion workstream.
