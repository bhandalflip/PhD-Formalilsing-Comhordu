# Make the model a class that every result takes

Date: 2026-10-22
Status: 2026-10-22 accepted

## Context

The Comhordú model is what any system that uses the protocol must supply: its modes and which of them are fail-safe, how one mode may change to another and how long that takes, the message latency, the maximum speed, the distances at which modes are compatible, and the constraints that relate them. It was stated as 28 global axioms. `safety` was proved from them, and a separate file built a concrete model that meets them, which showed that they are consistent. But Rocq could not link the two. `safety` was a theorem about the axioms, so nobody could apply it to that model, or to a real system's, and get a safety theorem for it that Rocq checks.

## Decision

The model is a class, with one field for each former axiom, under the same name. Every file outside the general library states its results in a section that takes a model of the class, so each result that uses the model takes it as an argument, which later files fill in by themselves. `safety` therefore holds for every model. The concrete model stays, as a value of the class that is never registered as an instance.

## Consequences

- `safety` rests only on standard-library axioms, and anyone can apply it to their own model and have Rocq check the result.
- Statements and proofs read as before. A few lines of proof changed, where a tactic could not find the model by itself.
- Rocq ends a section's tactics and notations with it. So each file defines the tactics that later files use outside its section, and restates their notations after it.
- No file may register an instance of the class, so that no result is quietly about one particular model.

## Rationale

The language already takes the protocol's process names and definitions as class parameters in sections, so the model follows the same pattern rather than adding a second one. A class keeps every statement and proof as it was, and it is the usual way to parametrise a large development in Rocq.

## Revisit when

A single result needs two models at once, or Rocq gains parameters that span files.

## Alternatives considered

### Keep the global axioms

Nothing changes, and the concrete model still shows that the axioms are consistent. But `safety` stays a theorem about the axioms rather than about every model, so applying it to a real system means trusting an argument made outside Rocq.

### A module type, with each file a functor over it

This is the classic way to parametrise a development by a structure, and the original plan for this change named it. Statements would need no implicit arguments. But applying a functor twice gives two copies of its types that don't fit together, and most files import several earlier ones. So each file would have to include every file before it, copying their contents, or take each of them as one more functor argument. Either is heavy, and every name from another file would gain a module path.

### A class, written into every statement

Each result would take the model through its own binder, without sections, so tactics and notations could stay where they are. But that touches some 1,500 statements and definitions, where sections need three lines per file.

## Implementation notes

- **The class.** `ComhModel` in `src/model/ComhBasics.v` has the 28 fields in the former axioms' order. The notation `m1 -mtr-> m2` is declared after it. Each file takes the model as `Context {Model : ComhModel}.`. No other name in the code is `Model`, so it clashes with no name a proof uses.
- **What a section keeps, in Rocq 9.2.** Results and definitions are generalised over the section variables they use, so those that don't use the model don't take it. Coercions, `#[export]` and `#[global]` instances, `#[global] Arguments` and `#[global] Open Scope` survive the section. Tactics and notations don't, and inside a section Rocq refuses a global attribute on either. Plain `Instance`, `Arguments` and `Open Scope` don't survive either. A top-level `Open Scope` is opened again in every file that imports it, and `#[global]` keeps that true inside a section.
- **Tactics.** A tactic that later files use, or that such a tactic calls, moved above its file's section when it names nothing from the file, and below it otherwise: 11 in `LanguageFoundations.v`, 41 in `ProtAuxResults.v`, 3 in `EntAuxResults.v` and 6 in `NetAuxBasics.v`. In `ProtAuxResults.v`, `backtrack_shape` names a lemma of its own file and is used later in it, so the section closes around it, and that file has two sections.
- **Notations.** Each file restates its notations after its section: 13 in `LanguageFoundations.v`, 12 in `InterfaceLanguage.v` and 6 in `ModeStateLanguage.v`, as `SoftwareLanguage.v`, `EntityLanguage.v` and `NetworkLanguage.v` already did. Reserved notations name nothing, so they moved above the sections.
- **Proof changes.** `replace c1 with c2`, without `by`, elaborates `c1` without looking for class instances, so it finds the model only when `c1` occurs in the goal. `boundedMovement` in `src/lang/NetworkLanguage.v` names it, as `@speedMax Model`. In `src/protocol/NARInsuff.v`, `dependent induction` now leaves a trivial equation in the induction hypotheses of `instant_insuff_abort` and `instant_insuff_bad` that it used to remove, and `lets …; try reflexivity` closes it.
- **The functor test.** With `Module A (M : P). Inductive val := vMode (m : M.Mode). End A.`, a functor `C` that applies both `A M` and a functor `B M` that itself applies `A M` cannot pass its `AA.val` to `B`'s functions, which expect `BB.AA.val`.
- **Assumptions.** `Print Assumptions safety` lists the 6 standard-library axioms and nothing else. `Print Assumptions concrete_model` lists two, both behind the standard library's reals. The record in `src/model/ModelConsistency.v` that copied the axioms, and `global_model`, which showed that the axioms fill it, are gone, since the class replaces them.
- **Rules.** The section pattern, and the ban on instances of the class, are in [`src/AGENTS.md`](../../src/AGENTS.md).
