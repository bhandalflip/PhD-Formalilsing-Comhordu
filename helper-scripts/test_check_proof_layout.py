#!/usr/bin/env python3
"""Test check_proof_layout.py on the corners of Rocq's syntax and of the layout rule.

Each case is a small Rocq file: some follow the layout, some break it, and every one that
follows it must still pass with its whitespace changed: its line endings, tabs, trailing spaces
and blank lines. Rocq compiles every case, as `make` does, and the checker reads the sentences
that Rocq found in it, so the tests need `rocq` on the PATH.

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
    "Definition d (* a (* b *) := *) : nat.": True,
    'Definition d (* "*)" *) := 1.': False,
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

# The kinds of whitespace change that a case which breaks the layout is also tested under.
KEEP_PROBLEMS = ("CRLF line endings", "tabs for indentation", "trailing spaces and tabs")


def compile_case(workdir, name, text):
    """Write a case to workdir and compile it with Rocq, as `make` does. Return its path, or
    None if Rocq refuses it."""
    path = os.path.join(workdir, name + ".v")
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(text)
    r = subprocess.run(["rocq", "compile", "-time-file", path + ".timing", path],
                       cwd=workdir, capture_output=True)
    return path if r.returncode == 0 else None


def sentences_by_hand(text, parts):
    """The sentences of a text, given their texts in order, for a file that Rocq refuses."""
    sentences, at = [], 0
    for part in parts:
        at = text.index(part, at)
        sentences.append((at, at + len(part)))
        at += len(part)
    return sentences


class CheckProofLayout(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        if not shutil.which("rocq"):
            raise RuntimeError("the tests compile their cases with Rocq: put rocq on the PATH")
        cases = {(name, None): text for name, text in GOOD.items()}
        cases.update({(name, None): text for name, (text, _) in BAD.items()})
        for name, text in GOOD.items():
            for noise, change in NOISE.items():
                if (name, noise) != ("one-line proof of 80 characters", "deeper indentation"):
                    cases[(name, noise)] = change(text)  # indentation counts in a line's length
        for name, (text, _) in BAD.items():
            cases.update({(name, noise): NOISE[noise](text) for noise in KEEP_PROBLEMS})
        cls.workdir = tempfile.TemporaryDirectory()
        keys = list(cases)
        with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 2) as pool:
            paths = pool.map(lambda i: compile_case(cls.workdir.name, f"Case{i}", cases[keys[i]]),
                             range(len(keys)))
        cls.compiled = {key: (cases[key], path) for key, path in zip(keys, paths)}

    @classmethod
    def tearDownClass(cls):
        cls.workdir.cleanup()

    def problems(self, name, noise=None):
        """The problems the checker finds in a case, from the sentences Rocq found in it."""
        text, path = self.compiled[(name, noise)]
        self.assertIsNotNone(path, "Rocq refuses the case")
        return sorted(cpl.check_text(text, cpl.rocq_sentences(path, text)))

    def test_good_layouts_pass(self):
        for name in GOOD:
            with self.subTest(name):
                self.assertEqual(self.problems(name), [])

    def test_bad_layouts_fail_where_expected(self):
        for name, (_, expected) in BAD.items():
            with self.subTest(name):
                problems = self.problems(name)
                self.assertEqual([line for line, _ in problems],
                                 [line for line, _ in expected], problems)
                for (_, message), (_, part) in zip(problems, expected):
                    self.assertIn(part, message)

    def test_whitespace_never_matters(self):
        for name, noise in self.compiled:
            if name in GOOD and noise:
                with self.subTest(name, noise=noise):
                    self.assertEqual(self.problems(name, noise), [])

    def test_whitespace_keeps_the_same_problems(self):
        for name in BAD:
            for noise in KEEP_PROBLEMS:
                with self.subTest(name, noise=noise):
                    self.assertEqual(self.problems(name, noise), self.problems(name))

    def test_sentences_are_read_in_characters(self):
        # Rocq counts bytes, and `ú` takes two.
        text, path = self.compiled[("unicode", None)]
        sentences = cpl.rocq_sentences(path, text)
        self.assertEqual([text[s:e] for s, e in sentences],
                         ["Lemma ú : True.", "Proof.", "exact I.", "Qed."])

    def test_which_sentences_open_a_proof(self):
        for text, opens in OPENS.items():
            with self.subTest(text):
                self.assertEqual(cpl.opens_proof(cpl.blank_out(text)), opens)

    def test_what_a_proof_sentence_does(self):
        for text, kind in PROOF_STARTS.items():
            with self.subTest(text):
                self.assertEqual(cpl.proof_start(cpl.blank_out(text)), kind)

    def test_statement_without_proof_is_skipped(self):
        # Rocq refuses this file, but the checker must not take b's proof for a's.
        text = "Lemma a : True.\nLemma b : True.\nProof. exact I. Qed.\n"
        sentences = sentences_by_hand(
            text, ["Lemma a : True.", "Lemma b : True.", "Proof.", "exact I.", "Qed."])
        self.assertEqual(cpl.check_text(text, sentences), [])

    def test_missing_stale_or_unreadable_sentences(self):
        text = GOOD["multi-line proof"]
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "A.v")
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
            with self.assertRaisesRegex(cpl.NoSentences, "missing"):
                cpl.rocq_sentences(path, text)
            self.assertIsNotNone(compile_case(d, "A", text))
            later = os.path.getmtime(path + ".timing") + 10
            os.utime(path, (later, later))
            with self.assertRaisesRegex(cpl.NoSentences, "older"):
                cpl.rocq_sentences(path, text)
            os.utime(path, (0, 0))
            with open(path + ".timing", "w", encoding="utf-8") as f:
                f.write("no sentences here\n")
            with self.assertRaisesRegex(cpl.NoSentences, "format"):
                cpl.rocq_sentences(path, text)
            with open(path + ".timing", "w", encoding="utf-8") as f:
                f.write("Chars 0 - 999 [Lemma~a~:~True.] 0. secs (0.u,0.s)\n")
            with self.assertRaisesRegex(cpl.NoSentences, "doesn't match"):
                cpl.rocq_sentences(path, text)

    def test_a_file_of_comments_has_no_sentences(self):
        text, path = self.compiled[("only comments", None)]
        self.assertEqual(cpl.rocq_sentences(path, text), [])

    def test_default_files_are_the_built_ones_without_vendored_code(self):
        files = cpl.default_files()
        self.assertIn(os.path.join(cpl.ROOT, "src", "protocol", "Main.v"), files)
        self.assertFalse([f for f in files if f.startswith(cpl.VENDORED + os.sep)])
        self.assertTrue(all(os.path.isfile(f) for f in files))

    def test_main_reports_problems_and_exit_codes(self):
        with tempfile.TemporaryDirectory() as d:
            good = compile_case(d, "Good", GOOD["multi-line proof"])
            bad = compile_case(d, "Bad", BAD["no Proof"][0])
            unbuilt = os.path.join(d, "Unbuilt.v")
            with open(unbuilt, "w", encoding="utf-8") as f:
                f.write(GOOD["multi-line proof"])
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                self.assertEqual(cpl.main([good]), 0)
                self.assertEqual(cpl.main([good, bad]), 1)
                self.assertEqual(cpl.main([good, bad, unbuilt]), 2)
            self.assertIn("Bad.v:2: a: start the proof with `Proof.`", out.getvalue())
            self.assertNotIn("Good.v", out.getvalue())
            self.assertIn("Unbuilt.v are missing: run `make`", err.getvalue())


if __name__ == "__main__":
    unittest.main()
