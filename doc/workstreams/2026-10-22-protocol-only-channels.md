# Workstream: Protocol-only channels

**STUB - FULL WORKSTREAM PLAN TBD**

| | |
|---|---|
| **Started** | 2026-10-22 |
| **Status** | 🧑 Stub: not started |
| **Goal** | Decide whether the channels that only the protocol uses should come from the protocol rather than the language, and if so, move them. |

**Legend:** 🤖 Agent · 🧑 Human-in-the-loop · ✅ / `[x]` done · `[ ]` to do

## Plan

- [ ] 🧑 **1. Analyse.** Five of the language's channels in [`src/lang/LanguageFoundations.v`](../../src/lang/LanguageFoundations.v) are used only by the protocol: `chanTrans`, `chanWake`, `chanPause`, `chanUnpause` and `chanBad`. Decide whether the protocol should supply them instead, as it has supplied its process names and definitions since [#3](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/3), and if so, plan the steps. The expression operators stay: they wrap the model's functions, so they belong with the model.

## Final phase

- [ ] 🤖 **Delete this workstream** once every other step is ticked or dropped, after moving anything that must outlive it, as [`AGENTS.md`](AGENTS.md) says.

## Log

- **2026-10-22:** Started as a stub, from a step of the Rocq upgrade and proof completion workstream.
