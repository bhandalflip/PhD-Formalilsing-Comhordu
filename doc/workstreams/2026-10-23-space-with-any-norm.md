# Workstream: Space with any norm

**STUB - FULL WORKSTREAM PLAN TBD**

| | |
|---|---|
| **Started** | 2026-10-23 |
| **Status** | 🧑 Stub: not started |
| **Goal** | Decide whether to let space be any space with a norm, rather than the plane with its usual distance, and if so, do it. |

**Legend:** 🤖 Agent · 🧑 Human-in-the-loop · ✅ / `[x]` done · `[ ]` to do

## Plan

- [ ] 🧑 **1. Analyse.** The language fixes space as the plane with its usual distance: `Position` and `dist2d` in [`src/lib/StandardResults.v`](../../src/lib/StandardResults.v). But the proof seems to use only what any norm gives: symmetry, the triangle inequality, and how distance behaves when positions are shifted or scaled, as in `distAddPres` and `displacement_scale`. Analyse whether positions can come from any space with a norm, such as through a class of their own, and plan the steps that make them so. The plane with Manhattan distance would be one instance, and a single coordinate, as for the road in the README's section on collision freedom, another. This changes definitions, so each change needs approval.

## Final phase

- [ ] 🤖 **Delete this workstream** once every other step is ticked or dropped, after moving anything that must outlive it, as [`AGENTS.md`](AGENTS.md) says.

## Log

- **2026-10-23:** Started as a stub, from the review of the README rewrite.
