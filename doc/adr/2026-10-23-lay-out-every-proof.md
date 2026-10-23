# Lay out every proof from `Proof.` to `Qed.`, and add a CI check for the layout

Date: 2026-10-23
Status: 2026-10-23 accepted

## Context

Half the proofs had no `Proof.`, and many of those began on the line where their statement ended. A statement's later lines and its proof were both indented by two spaces, so a reader couldn't see where one ended and the other began. The other half followed the standard layout, so the code mixed two styles, and nothing stopped new code from adding to either.

## Decision

Every proof starts with `Proof.` on a new line after its statement and ends with its closer, such as `Qed.`, on a line of its own, with the proof indented by two spaces between them. A short proof may instead take one line of at most 80 characters, as `Proof. auto. Qed.`. A script checks these line breaks and that length, and nothing else about whitespace. It takes each file's sentences from Rocq itself, which records them during every build, and CI runs it as a step of the build, after the script's own tests.

## Consequences

- Every statement stands apart from its proof, and every proof reads the same way.
- A pull request that breaks the layout fails CI, which names the file, the line and the fix.
- Apart from those line breaks and that length, whitespace never fails CI: not indentation, blank lines, tabs, trailing spaces or line endings.
- The check reads the language exactly as Rocq does, however Rocq changes, but it needs a build first.
- The project keeps its own checker, a short script, since there is no Rocq linter to borrow.

## Rationale

The Rocq manual recommends this layout, and the standard library, MathComp and CompCert use it in nearly every proof. All three also let a short proof sit on one line, which keeps a one-tactic proof from taking three lines, and the cap stops a long proof from being squashed onto one. Taking the sentences from Rocq leaves the checker none of the language to copy, so it can't drift from it, and recording them costs the build no time.

## Revisit when

Rocq gains a formatter or a linter that can check this layout.

## Alternatives considered

### Leave the layout as it is

Nothing would change. But statements would stay hard to tell from their proofs, and the code would keep two styles.

### Always put `Proof.` and `Qed.` on lines of their own

This is the simplest rule, with nothing to measure. But every one-tactic proof would take three lines, which none of the three projects asks for, and the files would grow without reading any better.

### One-line proofs without a cap, or with a cap on their tactics

Without a cap, a long proof could still be squashed onto one line. A cap on the number of tactics would still let long tactics through, and what a reader sees is the length of the line. 80 characters is MathComp's line width, and nearly all of the code's one-line proofs fit in it.

### The rule alone, with no check

There would be no code to maintain. But nothing would stop the layout drifting back, since people and agents both forget rules.

### An existing linter

There is none to borrow. The two Rocq linters that exist are unfinished and long untouched, and the standard library's own linter checks no layout beyond whitespace.

### A lexer of our own

A copy of the few rules of Rocq's lexer that matter here is short and fast, and needs no build. One matched Rocq on every sentence it was compared on. But Rocq's language changes, and a copy could fall behind it without anything noticing.

### A check of its own, apart from the build

A separate check would show a layout problem apart from a broken proof. But it needs Rocq's sentences, and here only a full compile gives them: Rocq's faster mode, which skips proofs, can't skip these, because every result sits in a section. So a separate check would have to compile everything again, or wait for the build and copy its files, and would save no time either way.

## Implementation notes

- **The survey**, counted by a one-off script:

  | | Proofs | Start with `Proof.` | One-line proofs | Multi-line proofs that end with `Qed.` on its own line | Proof indented by |
  |---|---|---|---|---|---|
  | Rocq 9.2's core and standard libraries, all 648 files | 13,264 | 98% | 19% | 99.9% | 0, 1 or 2 |
  | MathComp 2.2.0: `ssrnat`, `seq`, `fintype`, `bigop`, `ssralg` | 2,475 | all but 1 | 73% | all | 0 |
  | CompCert: `Coqlib`, `Integers`, `Values`, `Memory`, `Events`, `Allocproof`, `Cshmgenproof` | 1,256 | all | 4% | all | 2, mostly |
  | This repository before the change | 1,235 | 49% | 17% | 58% | 2 |

  Before the change, 350 of this repository's 626 proofs without `Proof.` began on their statement's last line. The Rocq 9.2 manual says of `Proof`, in `doc/sphinx/proofs/writing-proofs/proof-mode.rst`: "It is a good practice to use Proof as an opening parenthesis, closed in the script with a closing Qed." The [Coq wiki's style page](https://github.com/coq/coq/wiki/CoqStyle) says: "Start the proofs using a line containing `Proof.`"
- **Linters.** [vstyle-tools](https://github.com/appliedfm/vstyle-tools) says it is "under development and not ready for use", and its last commit is from January 2022. [coq-lint](https://github.com/magaud/coq-lint) is a prototype built on Coq 8.18 whose one feature turns a proof into a single line. The request for a Rocq linter, [rocq-prover/rocq#7976](https://github.com/coq/coq/issues/7976), has been open since 2018. The standard library's linter, `dev/lint-repository.sh`, checks that every commit builds, and for tabs, trailing spaces and final newlines.
- **Rocq's sentences.** The top-level `Makefile` sets `TIMING=1`, so when `make` compiles a file, Rocq writes `X.v.timing` beside it, with one line per sentence, `Chars START - END [...]`, where START and END are byte offsets. Two clean builds each way took 178 and 178 seconds without it, and 173 and 180 with it. `make clean` deletes the files, and `.gitignore` ignores them. The checker, [`helper-scripts/check_proof_layout.py`](../../helper-scripts/check_proof_layout.py), reads them for every file that `_CoqProject` builds, except the vendored ones in `src/lib/Extras/`. It stops with an error if one is missing, older than its file, or names no sentence, which would mean that the format of Rocq's timing output has changed.
- **Why not a faster pass.** `rocq compile -vos` skips the proofs that end with `Qed` and still reports every sentence. But inside a section, Rocq must run a proof to learn which section variables it uses, unless the proof says so with `Proof using`, and every result here sits in a section that takes the model. A clean `make vos` took 191 seconds, no less than the build.
- **What it checks.** A proof runs from a statement to its first closer: `Qed`, `Defined`, `Admitted`, `Abort` or `Save`. The statements are `Lemma`, `Theorem`, `Corollary`, `Proposition`, `Fact`, `Remark`, `Property` and `Goal`, and `Definition`, `Example`, `Instance`, `Fixpoint`, `CoFixpoint` and `Let` when they have no body, after any attributes and modifiers such as `Local`. To tell them apart, the checker reads the first words of each sentence, with its comments and strings blanked out. It doesn't know every command that opens a proof, such as `Next Obligation`, `Add Morphism` and `Function`, and leaves their proofs alone. `Proof using …` and `Proof with …` count as `Proof.`, and `Proof term.` is a whole proof in one sentence. The 80-character cap counts the whole line, indentation included, but not trailing blanks. A comment may sit anywhere, between a statement and its `Proof.` too.
- **Tests**, in [`helper-scripts/test_check_proof_layout.py`](../../helper-scripts/test_check_proof_layout.py): 38 layouts that must pass, 27 that must fail with given problems at given lines, 6 kinds of whitespace change that must change no verdict, tables of which sentences open a proof and what a `Proof` sentence does, and timing files that are missing, out of date or unreadable. Rocq compiles 373 cases, as `make` does, and the checker reads the sentences that Rocq found. Of 28 bugs planted in the checker one at a time, the tests catch all 28.
- **Checked on real code.** An earlier version of the checker had a lexer of its own, which matched Rocq on all 92,665 sentences it was compared with: every file in `src/` before and after the change, and 150 files picked at random from the standard library's 583. On the code before the change, and on those 150 files, the checker gives exactly the report that version gave: 1,074 problems in `src/`, and 112 in the standard library's files, each a real departure from this layout.
- **The change.** 626 proofs gained `Proof.`, and 137 of them stayed on one line. 454 closers moved to a line of their own, 19 one-line proofs longer than 80 characters spread over lines, and 56 closers moved to their statement's column. Where a proof gained `Proof.`, a comment that sat before its first tactic, such as a `(*Proof: …*)` sketch, now follows `Proof.`, which spread 2 more one-line proofs over lines. 15 proofs already had `Proof.` after such a comment, and keep it there.
- **Nothing else changed.** With blanks and `Proof.` removed, every file is as it was. Rocq's sentences are the same, in the same order, apart from the 626 new `Proof.`s, and every comment is unchanged. A clean build passes with the same warnings, and `safety` still rests on no unproved result and on the same 6 standard-library axioms.
- **CI.** The build job in [`.github/workflows/build.yml`](../../.github/workflows/build.yml) runs the checker's tests and then the checker, each as a step of its own, after the build and the report of what `safety` rests on.
- **The rule** is in [`src/AGENTS.md`](../../src/AGENTS.md).
