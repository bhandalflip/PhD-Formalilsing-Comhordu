# src/: rules for the Rocq development

## Layout

- The code is in four folders: [`lib/`](lib/README.md), [`model/`](model/README.md), [`lang/`](lang/README.md) and [`protocol/`](protocol/README.md). A file may import only from its own folder and the folders listed before it.

## Statements are frozen; proofs are not

- **Never change the statement** of an existing `Lemma`, `Theorem`, `Conjecture`, `Definition`, `Inductive`, `Record` or `Fixpoint` without human approval, and never delete a definition or an unproved result. If one is false or mis-stated, leave it `Admitted` and write it up in a report (see `doc/reports/AGENTS.md`).
- **Prefer one abstraction to many special cases.** The heuristic is mathematical elegance: a general result that makes several specific proofs a line each is worth more than the specific proofs. State it in the first folder that can, re-prove the specific results from it, and delete a proved result that nothing needs any more. Such deletions need no approval and are encouraged, as long as the statement of `safety` and what it rests on stay the same and the PR lists each deleted result with the one that replaced it.
- **Prove as stated.** Replace `Admitted.` with a complete proof ending in `Qed.`. Turn a `Conjecture` into a `Lemma` with the same name and statement.
- **When a statement turns out false**, and a human agrees to change it, keep its intent: add a well-formedness or well-typedness hypothesis that makes the original conclusion hold, where the language can express one, rather than weakening the conclusion. Weaken it only when no such hypothesis exists, and say so in the PR.
- **Don't add** `Axiom`, `Parameter`, `Conjecture`, `Hypothesis`/`Variable` outside a section, `Admitted`, `admit`, or the LibTactics `skip`.
- **Extra logical axioms:** the stdlib's classical logic, functional extensionality and proof irrelevance (already in the trust base) are allowed. Any newly used one must be listed in the PR and the report.

## Markers and conventions

- `Admitted (* UPGRADE-BROKEN *)` marks a proof that broke in a toolchain upgrade and couldn't be fixed on the spot.
- Trailing labels such as `Admitted (*4*)`, `(*R*)`, `(*D- foo*)` and `(*#tag*)` are the 2015 triage labels; see [`doc/archive/README.md`](../doc/archive/README.md). Remove a label together with its `Admitted` when the proof lands.
- Read the `(*Proof: …*)` sketch comments before proving. Keep them.
- Write an intro pattern with a space after its bracket, as `[ | x]`: `[|` is a token of the entity notation `[| p, l, h, k |]`, so `[|x]` fails to parse once `EntityLanguage` is imported.
- **Helper lemmas** go immediately before the lemma that first needs them. Mark them `Local`: that, not the name, is what says a result is auxiliary.
- **Name every result by what it states**, helpers included. Only a helper that states nearly what the result it supports states takes that result's name with `_aux`, `_aux2`, …

## Libraries and tactics

- Import the stdlib explicitly: `From Stdlib Require Import …`.
- Import project modules by their full path, as `Require Import ComhCoq.<folder>.<Module>.` (existing style) or `From ComhCoq.<folder> Require Import <Module>.`.
- For real-number goals, prefer `lra`/`nra`/`lia` over the hand-rolled lemmas in `lib/RInequalities.v`/`lib/StandardResults.v`. Reach for mathcomp-analysis's `Rstruct` bridge only when the stdlib lacks a lemma (see `doc/adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md`).

## Checks before committing

- `make` must succeed from clean.
- `make assumptions` must not gain any new entry except proofs that left the list.
