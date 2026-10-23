#!/usr/bin/env python3
"""Test check_proof_layout.py on the corners of Rocq's syntax and of the layout rule.

Each case is a small Rocq file: some follow the layout, some break it, and every one that
follows it must still pass with its whitespace changed, its line endings, tabs, trailing spaces
and blank lines. Where `rocq` is on the PATH, each case is also compiled with `rocq compile
-time`, which prints where every sentence starts and ends, to check that the checker splits
sentences exactly as Rocq does.

Usage: python3 helper-scripts/test_check_proof_layout.py   (from the repository root)
"""
import concurrent.futures
import contextlib
import io
import os
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_proof_layout as cpl  # noqa: E402

def rocq(text):
    """The text of a case, written below as an indented, triple-quoted string. The line break
    after the opening quotes and the indentation that every line shares are dropped, and all
    other whitespace is kept as written. The strings are raw, so `/\\` needs no escaping."""
    assert text.startswith("\n")
    return textwrap.dedent(text[1:])


def one_liner(length):
    """A lemma whose one-line proof has exactly `length` characters."""
    bare = 'Proof. idtac "". exact I. Qed.'
    return "Lemma a : True.\n" + bare.replace('""', '"' + "x" * (length - len(bare)) + '"') + "\n"


# Cases that follow the layout: the checker must find no problem in them.
GOOD = {
    "multi-line proof": rocq(r"""
        Lemma a : True.
        Proof.
          exact I.
        Qed.
        """),
    "one-line proof": rocq(r"""
        Lemma a : True.
        Proof. exact I. Qed.
        """),
    "one-line proof of 80 characters": one_liner(80),
    "empty file": "",
    "only comments": rocq(r"""
        (* Lemma a : True. exact I. Qed. *)
        """),
    "proofs back to back": rocq(r"""
        Lemma a : True.
        Proof. exact I. Qed.
        Lemma b : True.
        Proof.
          exact I.
        Qed.


        Theorem c : True.
        Proof. exact I. Qed.
        """),
    "every kind of result": rocq(r"""
        Theorem a : True.
        Proof. exact I. Qed.
        Corollary b : True.
        Proof. exact I. Qed.
        Proposition c : True.
        Proof. exact I. Qed.
        Fact d : True.
        Proof. exact I. Qed.
        Remark e : True.
        Proof. exact I. Qed.
        Property f : True.
        Proof. exact I. Qed.
        """),
    "goal": rocq(r"""
        Goal True.
        Proof.
          exact I.
        Qed.
        """),
    "local and attributes": rocq(r"""
        Local Lemma a : True.
        Proof. exact I. Qed.
        #[local] Lemma b : True.
        Proof. exact I. Qed.
        #[ local ]
        Lemma c : True.
        Proof. exact I. Qed.
        """),
    "Proof using": rocq(r"""
        Section S.
        Variable n : nat.
        Lemma a : n = n.
        Proof using n.
          reflexivity.
        Qed.
        End S.
        """),
    "Proof with and an ellipsis": rocq(r"""
        Lemma a : True.
        Proof with auto.
          idtac...
        Qed.
        """),
    "Proof term": rocq(r"""
        Lemma a : True.
        Proof I.
        Lemma b : True.
        Proof. exact I. Qed.
        """),
    "Proof term in brackets": rocq(r"""
        Lemma a : True /\ True.
        Proof (conj I I).
        """),
    "spaces before dots": rocq(r"""
        Lemma a : True .
        Proof .
          exact I .
        Qed .
        """),
    "Defined": rocq(r"""
        Definition d : nat.
        Proof.
          exact 0.
        Defined.
        """),
    "Admitted": rocq(r"""
        Lemma a : True.
        Admitted.
        Lemma b : True.
        Proof.
          idtac.
        Admitted.
        """),
    "Abort": rocq(r"""
        Lemma a : False.
        Proof.
          idtac.
        Abort.
        """),
    "definitions with bodies": rocq(r"""
        Definition two := 2.
        Definition three : nat := 3.
        Example e := 1.
        Fixpoint f (n : nat) : nat := n.
        Lemma a : True.
        Proof. exact I. Qed.
        """),
    "definition with a let binder": rocq(r"""
        Definition d (x := 1) : nat.
        Proof.
          exact x.
        Defined.
        """),
    "instances": rocq(r"""
        Class C := { c : nat }.
        #[local] Instance i : C := {| c := 1 |}.
        #[local] Instance j : C.
        Proof.
          exact {| c := 0 |}.
        Defined.
        """),
    "example": rocq(r"""
        Example e : 1 = 1.
        Proof. reflexivity. Qed.
        """),
    "let in a section": rocq(r"""
        Section S.
        Let l : nat.
        Proof.
          exact 0.
        Defined.
        End S.
        """),
    "statement over several lines": rocq(r"""
        Lemma a :
          (* a comment. with dots. *)
          True /\
          True.
        Proof.
          split; exact I.
        Qed.
        """),
    "comments around the proof": rocq(r"""
        Lemma (* c *) a : True. (* hard *)
        (*Proof: trivial.*)

        Proof. (* sketch *)
          exact I. (* done *)
        Qed. (* end *)
        Lemma b : True.
        Proof. exact I. Qed. (* short *)
        """),
    "comment before the closer": rocq(r"""
        Lemma a : True.
        Proof.
          exact I.
        (* end *) Qed.
        """),
    "nested comments and strings in comments": rocq(r"""
        (* outer (* inner. Qed. *) "a string with *) in it" still a comment. *)
        Lemma a : True.
        Proof. exact I. Qed.
        """),
    "strings with dots and quotes": rocq(r"""
        Lemma a : True.
        Proof.
          idtac "a. (* Qed."; idtac "say ""hi"". Qed.".
          exact I.
        Qed.
        """),
    "qualified names": rocq(r"""
        Lemma a : Nat.add 0 0 = 0.
        Proof. reflexivity. Qed.
        """),
    "recursive notation": rocq(r"""
        Notation "[[ x ; .. ; y ]]" := (cons x .. (cons y nil) ..).
        Lemma a : [[1 ; 2]] = cons 1 (cons 2 nil).
        Proof. reflexivity. Qed.
        """),
    "keywords inside names": rocq(r"""
        Definition Lemmas := 1.
        Definition Proofs := 2.
        Definition Qeds := 3.
        """),
    "bullets and braces": rocq(r"""
        Lemma a : True /\ (True /\ True).
        Proof.
          split.
          - exact I.
          - split.
            + exact I.
            + { exact I. }
        Qed.
        """),
    "deep bullets": rocq(r"""
        Lemma a : True /\ (True /\ (True /\ True)).
        Proof.
          split.
          - exact I.
          - split.
            + exact I.
            + split.
              * exact I.
              * exact I.
        Qed.
        """),
    "goal selector with a brace": rocq(r"""
        Lemma a : True /\ (True /\ True).
        Proof.
          split.
          2: { split.
               - exact I.
               - exact I. }
          exact I.
        Qed.
        """),
    "closing brace before the closer": rocq(r"""
        Lemma a : True.
        Proof.
          { exact I. }
        Qed.
        """),
    "unicode": rocq(r"""
        (* Comhordú *)
        Lemma ú : True.
        Proof. exact I. Qed.
        """),
    "module": rocq(r"""
        Module M.
          Lemma a : True.
          Proof. exact I. Qed.
          Lemma b : True.
          Proof.
            exact I.
          Qed.
        End M.
        """),
    "ltac mentioning Proof and Qed": rocq(r"""
        Ltac t := idtac "Proof. Qed.".
        Lemma a : True.
        Proof. t. exact I. Qed.
        """),
    "no final newline": rocq(r"""
        Lemma a : True.
        Proof. exact I. Qed."""),
}

# Cases that break the layout, with the problems the checker must report: (line, part of the
# message). The cases are valid Rocq, so their sentences can be checked against Rocq's too.
BAD = {
    "no Proof": (rocq(r"""
        Lemma a : True.
          exact I.
        Qed.
        """), [(2, "start the proof with `Proof.`")]),
    "no Proof, proof on the statement's line": (rocq(r"""
        Lemma a : True. exact I.
        Qed.
        """), [(1, "start the proof with `Proof.`")]),
    "no Proof, all on one line": (rocq(r"""
        Lemma a : True. exact I. Qed.
        """), [(1, "start the proof with `Proof.`")]),
    "no Proof, one-line proof": (rocq(r"""
        Lemma a : True.
        exact I. Qed.
        """), [(2, "start the proof with `Proof.`")]),
    "no Proof after a multi-line statement": (rocq(r"""
        Lemma a :
          True. exact I.
        Qed.
        """), [(2, "start the proof with `Proof.`")]),
    "no Proof after a sketch": (rocq(r"""
        Lemma a : True.
          (*Proof: trivial.*)
          exact I.
        Qed.
        """), [(3, "start the proof with `Proof.`")]),
    "no Proof in a goal": (rocq(r"""
        Goal True.
          exact I.
        Qed.
        """), [(2, "start the proof with `Proof.`")]),
    "no Proof in an instance": (rocq(r"""
        Class C := { c : nat }.
        #[local] Instance i : C.
          exact {| c := 0 |}.
        Defined.
        """), [(3, "start the proof with `Proof.`")]),
    "no Proof in a local lemma": (rocq(r"""
        Local Lemma a : True.
          exact I.
        Qed.
        """), [(2, "start the proof with `Proof.`")]),
    "no Proof after an attribute": (rocq(r"""
        #[local] Lemma a : True.
          exact I.
        Qed.
        """), [(2, "start the proof with `Proof.`")]),
    "no Proof after a let binder": (rocq(r"""
        Definition d (x := 1) : nat.
          exact x.
        Defined.
        """), [(2, "start the proof with `Proof.`")]),
    "Proof on the statement's line": (rocq(r"""
        Lemma a : True. Proof.
          exact I.
        Qed.
        """), [(1, "put `Proof.` on a new line after the statement")]),
    "Proof after a comment on the statement's line": (rocq(r"""
        Lemma a : True. (* c *) Proof.
          exact I.
        Qed.
        """), [(1, "put `Proof.` on a new line after the statement")]),
    "one-line proof on the statement's line": (rocq(r"""
        Lemma a : True. Proof. exact I. Qed.
        """), [(1, "put `Proof.` on a new line after the statement")]),
    "Proof term on the statement's line": (rocq(r"""
        Lemma a : True. Proof I.
        """), [(1, "put `Proof.` on a new line after the statement")]),
    "tactic after Proof": (rocq(r"""
        Lemma a : True.
        Proof. idtac.
          exact I.
        Qed.
        """), [(2, "put nothing after `Proof.` on its line")]),
    "Qed after the last tactic": (rocq(r"""
        Lemma a : True.
        Proof.
          exact I. Qed.
        """), [(3, "put `Qed.` on a line of its own")]),
    "Qed after the last tactic, with Proof using": (rocq(r"""
        Section S.
        Variable n : nat.
        Lemma a : n = n.
        Proof using n.
          reflexivity. Qed.
        End S.
        """), [(5, "put `Qed.` on a line of its own")]),
    "Qed after the last tactic, with Proof with": (rocq(r"""
        Lemma a : True.
        Proof with auto.
          idtac... Qed.
        """), [(3, "put `Qed.` on a line of its own")]),
    "Defined after the last tactic": (rocq(r"""
        Definition d : nat.
        Proof.
          exact 0. Defined.
        """), [(3, "put `Defined.` on a line of its own")]),
    "Qed after a comment after a tactic": (rocq(r"""
        Lemma a : True.
        Proof.
          exact I. (* c *) Qed.
        """), [(3, "put `Qed.` on a line of its own")]),
    "Qed after a brace": (rocq(r"""
        Lemma a : True.
        Proof.
          { exact I. } Qed.
        """), [(3, "put `Qed.` on a line of its own")]),
    "Qed after a bullet's tactic": (rocq(r"""
        Lemma a : True /\ True.
        Proof.
          split.
          - exact I.
          - exact I. Qed.
        """), [(5, "put `Qed.` on a line of its own")]),
    "statement after Qed": (rocq(r"""
        Lemma a : True.
        Proof.
          exact I.
        Qed. Lemma b : True.
        Proof.
          exact I.
        Qed.
        """), [(4, "put nothing after `Qed.` on its line")]),
    "definition after a one-line proof": (rocq(r"""
        Lemma a : True.
        Proof. exact I. Qed. Definition x := 1.
        """), [(2, "put nothing after `Qed.` on its line")]),
    "one-line proof of 81 characters": (one_liner(81), [(2, "at most 80 characters, not 81")]),
    "no Proof and Qed after the last tactic": (rocq(r"""
        Lemma a : True.
          idtac.
          exact I. Qed.
        """), [(2, "start the proof with `Proof.`"), (3, "put `Qed.` on a line of its own")]),
}

# Ways to change whitespace that must never change the checker's verdict.
NOISE = {
    "CRLF line endings": lambda t: t.replace("\n", "\r\n"),
    "tabs for indentation": lambda t: re.sub(r"(?m)^  ", "\t", t),
    "trailing spaces and tabs": lambda t: t.replace("\n", "  \t\n"),
    "blank lines between lines": lambda t: t.replace("\n", "\n\n"),
    "deeper indentation": lambda t: re.sub(r"(?m)^(?=\s)", "    ", t),
    "no indentation": lambda t: re.sub(r"(?m)^[ \t]+", "", t),
}

# Whether a sentence opens a proof.
OPENS = {
    "Lemma a : True.": True,
    "Local Lemma a : True.": True,
    "#[local] Lemma a : True.": True,
    "#[ local ]\nTheorem a : True.": True,
    "Polymorphic Lemma a : True.": True,
    "Goal True.": True,
    "Definition d : nat.": True,
    "Definition d (x := 1) : nat.": True,
    "Definition d := 1.": False,
    "Definition d : nat := 1.": False,
    "Instance i : C.": True,
    "#[local] Instance i : C := {| c := 1 |}.": False,
    "Example e : 1 = 1.": True,
    "Example e := 1.": False,
    "Let l : nat.": True,
    "Fixpoint f (n : nat) : nat := n.": False,
    "Program Definition p : nat := _.": False,
    "Conjecture c : True.": False,
    "Axiom ax : True.": False,
    "Definition Lemmas := 1.": False,
    "Ltac t := idtac.": False,
    "Proof.": False,
    "(* Lemma a : True. *) Check I.": False,
    "Lemma (* c *) a : True.": True,
    "#[local] (* c *) Lemma a : True.": True,
    "Definition d (* := 1 *) : nat.": True,
    'Example e : "a := b" = "a := b".': True,
}

# What a sentence that starts with `Proof` does: open the proof, or be the whole proof.
PROOF_STARTS = {
    "Proof.": "opens",
    "Proof .": "opens",
    "Proof using n.": "opens",
    "Proof using.": "opens",
    "Proof with auto.": "opens",
    "Proof I.": "whole",
    "Proof (conj I I).": "whole",
    "Proofs.": None,
    "Proof'.": None,
    "exact I.": None,
}

# None of these is valid Rocq, but the checker must not fail on them.
NOT_ROCQ = {
    "byte order mark": "\ufeff" + rocq(r"""
        Lemma a : True.
          exact I.
        Qed.
        """),
    "unterminated comment": rocq(r"""
        Lemma a : True.
        Proof. exact I. Qed.
        (* no end
        """),
    "unterminated string": rocq(r"""
        Lemma a : True.
        Proof. idtac "no end
        """),
    "statement with no proof": rocq(r"""
        Lemma a : True.
        """),
    "Proof with no statement": rocq(r"""
        Proof.
          exact I.
        Qed.
        """),
}


def rocq_sentences(text, workdir, name):
    """The sentences of a file as Rocq's `-time` output gives them, as (start, end) character
    offsets, or None if the file doesn't compile."""
    path = os.path.join(workdir, name + ".v")
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(text)
    r = subprocess.run(["rocq", "compile", "-time", path], cwd=workdir,
                       capture_output=True, encoding="utf-8", errors="replace")
    if r.returncode != 0:
        return None
    char_at, byte = {}, 0  # Rocq counts in bytes, the checker in characters
    for i, ch in enumerate(text):
        char_at[byte] = i
        byte += len(ch.encode("utf-8"))
    char_at[byte] = len(text)
    spans = re.findall(r"^Chars (\d+) - (\d+) \[", r.stdout, re.M)
    return [(char_at[int(s)], char_at[int(e)]) for s, e in spans]


class CheckProofLayout(unittest.TestCase):

    def test_good_layouts_pass(self):
        for name, text in GOOD.items():
            with self.subTest(name):
                self.assertEqual(cpl.check_text(text), [])

    def test_bad_layouts_fail_where_expected(self):
        for name, (text, expected) in BAD.items():
            with self.subTest(name):
                problems = sorted(cpl.check_text(text))
                self.assertEqual([line for line, _ in problems],
                                 [line for line, _ in expected], problems)
                for (_, message), (_, part) in zip(problems, expected):
                    self.assertIn(part, message)

    def test_whitespace_never_matters(self):
        for name, text in GOOD.items():
            for noise, change in NOISE.items():
                if name == "one-line proof of 80 characters" and noise == "deeper indentation":
                    continue  # indentation is part of a line's length
                with self.subTest(name, noise=noise):
                    self.assertEqual(cpl.check_text(change(text)), [])

    def test_whitespace_keeps_the_same_problems(self):
        for name, (text, expected) in BAD.items():
            for noise in ("CRLF line endings", "tabs for indentation", "trailing spaces and tabs"):
                with self.subTest(name, noise=noise):
                    self.assertEqual(cpl.check_text(NOISE[noise](text)), cpl.check_text(text))

    def test_which_sentences_open_a_proof(self):
        for text, opens in OPENS.items():
            with self.subTest(text):
                sentences, masked = cpl.lex(text)
                self.assertEqual(len(sentences), 1)
                self.assertEqual(cpl.opens_proof(masked, sentences[0]), opens)

    def test_what_a_proof_sentence_does(self):
        for text, kind in PROOF_STARTS.items():
            with self.subTest(text):
                sentences, masked = cpl.lex(text)
                self.assertEqual(cpl.proof_start(masked, sentences[0]), kind)

    def test_files_that_are_not_rocq_do_not_crash(self):
        for name, text in NOT_ROCQ.items():
            with self.subTest(name):
                self.assertIsInstance(cpl.check_text(text), list)

    def test_statement_without_proof_is_skipped(self):
        # Rocq refuses this file, but the checker must not take b's proof for a's.
        self.assertEqual(cpl.check_text("Lemma a : True.\nLemma b : True.\nProof. exact I. Qed.\n"),
                         [])

    def test_bom_is_skipped(self):
        problems = cpl.check_text(NOT_ROCQ["byte order mark"])
        self.assertEqual([line for line, _ in problems], [2])

    def test_sentences_match_rocq(self):
        if not shutil.which("rocq"):
            self.skipTest("rocq is not on the PATH")
        cases = dict(GOOD)
        cases.update({name: text for name, (text, _) in BAD.items()})
        for noise in ("CRLF line endings", "tabs for indentation", "blank lines between lines"):
            cases.update({f"{name}, {noise}": NOISE[noise](text) for name, text in GOOD.items()})
        with tempfile.TemporaryDirectory() as workdir:
            names = {name: f"Case{i}" for i, name in enumerate(cases)}
            with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 2) as pool:
                spans = dict(zip(cases, pool.map(
                    lambda name: rocq_sentences(cases[name], workdir, names[name]), cases)))
        for name, text in cases.items():
            with self.subTest(name):
                self.assertIsNotNone(spans[name], "the case doesn't compile")
                self.assertEqual(cpl.lex(text)[0], spans[name])

    def test_default_files_skip_vendored_code(self):
        files = cpl.default_files()
        self.assertIn(os.path.join(cpl.SRC, "protocol", "Main.v"), files)
        self.assertFalse([f for f in files if f.startswith(cpl.VENDORED + os.sep)])

    def test_main_reports_problems_and_exit_code(self):
        with tempfile.TemporaryDirectory() as d:
            good, bad = os.path.join(d, "Good.v"), os.path.join(d, "Bad.v")
            with open(good, "w") as f:
                f.write(GOOD["multi-line proof"])
            with open(bad, "w") as f:
                f.write(BAD["no Proof"][0])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(cpl.main([good]), 0)
                self.assertEqual(cpl.main([good, bad]), 1)
            self.assertIn("Bad.v:2: a: start the proof with `Proof.`", out.getvalue())
            self.assertNotIn("Good.v", out.getvalue())


if __name__ == "__main__":
    unittest.main()
