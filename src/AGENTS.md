# src/: rules for the Rocq development

## Layout

- The code is in four folders: [`lib/`](lib/README.md), [`model/`](model/README.md), [`lang/`](lang/README.md) and [`protocol/`](protocol/README.md). A file may import only from its own folder and the folders listed before it.

## Statements are frozen; proofs are not

- **Never change the statement** of an existing `Lemma`, `Theorem`, `Conjecture`, `Definition`, `Inductive`, `Record` or `Fixpoint` without human approval, and never delete a definition or an unproved result.
- **Prefer one abstraction to many special cases.** The heuristic is mathematical elegance: a general result that makes several specific proofs a line each is worth more than the specific proofs. State it in the first folder that can, re-prove the specific results from it, and delete a proved result that nothing needs any more. Such deletions need no approval and are encouraged, as long as the statement of `safety` and what it rests on stay the same and the PR lists each deleted result with the one that replaced it.
- **When a statement turns out false**, and a human agrees to change it, keep its intent: add a well-formedness or well-typedness hypothesis that makes the original conclusion hold, where the language can express one, rather than weakening the conclusion. Weaken it only when no such hypothesis exists, and say so in the PR.
- **Don't add** `Axiom`, `Parameter`, `Conjecture`, `Hypothesis`/`Variable` outside a section, `Admitted`, `admit`, or the LibTactics `skip`.
- **Extra logical axioms:** the stdlib's classical logic, functional extensionality and proof irrelevance (already in the trust base) are allowed. Any newly used one must be listed in the PR and the report.

## The model

- **Every file outside `lib/` takes the model in a section**, with `Context {Model : ComhModel}.` after its imports, so that its results hold for every model. When the section closes, Rocq adds the model as an argument to each result that uses it, and later files fill it in by themselves.
- **Rocq drops a section's tactics and notations when it closes.** Define a tactic that later files use outside the section: above it if it names nothing from its own file, else below it. Restate after the section each notation that later files use. Open a scope inside a section with `#[global] Open Scope`.
- **Never declare an instance of `ComhModel`**, not even `concrete_model`. Rocq would then supply it silently where a result is meant to hold for every model.
- `replace` can't find the model by itself when its first term isn't in the goal. Name the model there, as in `@speedMax Model`.

## Conventions

- Read the `(*Proof: …*)` sketch comments before proving. Keep them.
- Write an intro pattern with a space after its bracket, as `[ | x]`: `[|` is a token of the entity notation `[| p, l, h, k |]`, so `[|x]` fails to parse once `EntityLanguage` is imported.
- **Helper lemmas** go immediately before the lemma that first needs them. Mark them `Local`: that, not the name, is what says a result is auxiliary.
- **Name every result by what it states**, helpers included. Only a helper that states nearly what the result it supports states takes that result's name with `_aux`, `_aux2`, …
- **Lay out every proof** from `Proof.`, on a new line after its statement, to its closer, such as `Qed.`, on a line of its own, with the proof indented by 2 spaces between them. A short proof can instead take one line of at most 80 characters, as `Proof. auto. Qed.`. CI checks these line breaks and that length with [`check_proof_layout.py`](../helper-scripts/check_proof_layout.py), and the [ADR](../doc/adr/2026-10-23-lay-out-every-proof.md) says why.

## Libraries and tactics

- Import the stdlib explicitly: `From Stdlib Require Import …`.
- Import project modules by their full path, as `Require Import ComhCoq.<folder>.<Module>.` (existing style) or `From ComhCoq.<folder> Require Import <Module>.`.
- For real-number goals, prefer `lra`/`nra`/`lia` over the hand-rolled lemmas in `lib/RInequalities.v`/`lib/StandardResults.v`. Reach for mathcomp-analysis's `Rstruct` bridge only when the stdlib lacks a lemma (see `doc/adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md`).

## Checks before committing

- `make` must succeed from clean.
- `make assumptions` must not gain any new entry except proofs that left the list.
- `python3 helper-scripts/check_proof_layout.py` must find no problem.
