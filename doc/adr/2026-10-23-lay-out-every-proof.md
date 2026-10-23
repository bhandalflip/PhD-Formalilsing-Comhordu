# Lay out every proof from `Proof.` to `Qed.`, and check it in CI

Date: 2026-10-23
Status: 2026-10-23 accepted

## Context

Half the proofs had no `Proof.`, and many of those began on the line where their statement ended. A statement's later lines and its proof were both indented by two spaces, so a reader couldn't see where one ended and the other began. The other half followed the standard layout, so the code mixed two styles, and nothing stopped new code from adding to either.

## Decision

Every proof starts with `Proof.` on a new line after its statement and ends with its closer, such as `Qed.`, on a line of its own, with the proof indented by two spaces between them. A short proof may instead take one line of at most 80 characters, as `Proof. auto. Qed.`. A script checks these line breaks and that length, and CI runs it on every pull request, after the script's own tests. It checks nothing else about whitespace.

## Consequences

- Every statement stands apart from its proof, and every proof reads the same way.
- A pull request that breaks the layout fails CI, which names the file, the line and the fix.
- Apart from those line breaks and that length, whitespace never fails CI: not indentation, blank lines, tabs, trailing spaces or line endings.
- The project keeps its own checker, since there is no Rocq linter to borrow. Its tests compile their cases with Rocq, to check that it splits a file into sentences exactly as Rocq does.

## Rationale

The Rocq manual recommends this layout, and the standard library, MathComp and CompCert use it in nearly every proof. All three also let a short proof sit on one line, which keeps a one-tactic proof from taking three lines, and the cap stops a long proof from being squashed onto one.

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

### Rocq's own parser

Rocq's timing output gives the span of every sentence, so a check built on it could never disagree with Rocq. But it needs a full build first, which would make the check slow and tie it to the build. The few rules of Rocq's lexer that matter here are short to copy, and the tests compare the copy with Rocq.

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
- **The checker**, [`helper-scripts/check_proof_layout.py`](../../helper-scripts/check_proof_layout.py), follows Rocq 9.2's lexer, `parsing/cLexer.ml`:
  - The blanks are space, tab, newline and carriage return. A `.` ends a sentence when a blank or the end of the file follows it, which also covers `...`, but `..` is a token of its own and doesn't.
  - Between sentences, a run of `-`, `+` or `*` is a bullet and a `{` or `}` is a brace, each a sentence of its own, as is a goal selector with its brace, such as `2: {`.
  - Comments nest, and a string inside a comment hides any `*)` in it.
- **What it checks.** A proof runs from a statement to its first closer: `Qed`, `Defined`, `Admitted`, `Abort` or `Save`. The statements are `Lemma`, `Theorem`, `Corollary`, `Proposition`, `Fact`, `Remark`, `Property` and `Goal`, and `Definition`, `Example`, `Instance`, `Fixpoint`, `CoFixpoint` and `Let` when they have no body, after any attributes and modifiers such as `Local`. It doesn't know every command that opens a proof, such as `Next Obligation`, `Add Morphism` and `Function`, and leaves their proofs alone. `Proof using …` and `Proof with …` count as `Proof.`, and `Proof term.` is a whole proof in one sentence. The 80-character cap counts the whole line, indentation included, but not trailing blanks. A comment may sit anywhere, between a statement and its `Proof.` too.
- **Tests**, in [`helper-scripts/test_check_proof_layout.py`](../../helper-scripts/test_check_proof_layout.py): 38 layouts that must pass, 27 that must fail with given problems at given lines, 6 kinds of whitespace change that must change no verdict, 5 files that aren't valid Rocq, and tables of which sentences open a proof and what a `Proof` sentence does. Where `rocq` is on the `PATH`, 179 of the cases are compiled with `rocq compile -time`, which prints every sentence's span, and the checker must find the same spans. Of 31 bugs planted in the checker one at a time, the tests catch 30. The last treats a form feed as a blank, which changes nothing, since Rocq refuses a form feed outside comments and strings.
- **Checked against Rocq on real code.** The checker's sentences match Rocq's on every file in `src/`, before the change (24,457 sentences) and after it (25,083), and on 150 files picked at random from the standard library's 583 (43,125). It ran without failing on all 648 files of the core and standard libraries, the 5 of MathComp and the 7 of CompCert, and every problem it reported in a sample of each kind was a real departure from this layout.
- **The change.** 626 proofs gained `Proof.`, and 137 of them stayed on one line. 454 closers moved to a line of their own, 19 one-line proofs longer than 80 characters spread over lines, and 56 closers moved to their statement's column. Where a proof gained `Proof.`, a comment that sat before its first tactic, such as a `(*Proof: …*)` sketch, now follows `Proof.`, which spread 2 more one-line proofs over lines. 15 proofs already had `Proof.` after such a comment, and keep it there.
- **Nothing else changed.** With blanks and `Proof.` removed, every file is as it was. The sentences are the same, in the same order, apart from the 626 new `Proof.`s, and every comment is unchanged. A clean build passes with the same warnings, and `safety` still rests on no unproved result and on the same 6 standard-library axioms.
- **CI.** The job `layout` in [`.github/workflows/build.yml`](../../.github/workflows/build.yml) runs in the same image as the build, so that the tests can compile their cases.
- **The rule** is in [`src/AGENTS.md`](../../src/AGENTS.md).
