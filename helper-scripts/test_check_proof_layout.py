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
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_proof_layout as cpl  # noqa: E402

CLASS = "Class C := { c : nat }.\n"


def one_liner(length):
    """A lemma whose one-line proof has exactly `length` characters."""
    bare = 'Proof. idtac "". exact I. Qed.'
    return "Lemma a : True.\n" + bare.replace('""', '"' + "x" * (length - len(bare)) + '"') + "\n"


# Cases that follow the layout: the checker must find no problem in them.
GOOD = {
    "multi-line proof": "Lemma a : True.\nProof.\n  exact I.\nQed.\n",
    "one-line proof": "Lemma a : True.\nProof. exact I. Qed.\n",
    "one-line proof of 80 characters": one_liner(80),
    "empty file": "",
    "only comments": "(* Lemma a : True. exact I. Qed. *)\n",
    "proofs back to back": "Lemma a : True.\nProof. exact I. Qed.\nLemma b : True.\nProof.\n"
                           "  exact I.\nQed.\n\n\nTheorem c : True.\nProof. exact I. Qed.\n",
    "every kind of result": "Theorem a : True.\nProof. exact I. Qed.\nCorollary b : True.\n"
                            "Proof. exact I. Qed.\nProposition c : True.\nProof. exact I. Qed.\n"
                            "Fact d : True.\nProof. exact I. Qed.\nRemark e : True.\n"
                            "Proof. exact I. Qed.\nProperty f : True.\nProof. exact I. Qed.\n",
    "goal": "Goal True.\nProof.\n  exact I.\nQed.\n",
    "local and attributes": "Local Lemma a : True.\nProof. exact I. Qed.\n"
                            "#[local] Lemma b : True.\nProof. exact I. Qed.\n"
                            "#[ local ]\nLemma c : True.\nProof. exact I. Qed.\n",
    "Proof using": "Section S.\nVariable n : nat.\nLemma a : n = n.\nProof using n.\n"
                   "  reflexivity.\nQed.\nEnd S.\n",
    "Proof with and an ellipsis": "Lemma a : True.\nProof with auto.\n  idtac...\nQed.\n",
    "Proof term": "Lemma a : True.\nProof I.\nLemma b : True.\nProof. exact I. Qed.\n",
    "Proof term in brackets": "Lemma a : True /\\ True.\nProof (conj I I).\n",
    "spaces before dots": "Lemma a : True .\nProof .\n  exact I .\nQed .\n",
    "Defined": "Definition d : nat.\nProof.\n  exact 0.\nDefined.\n",
    "Admitted": "Lemma a : True.\nAdmitted.\nLemma b : True.\nProof.\n  idtac.\nAdmitted.\n",
    "Abort": "Lemma a : False.\nProof.\n  idtac.\nAbort.\n",
    "definitions with bodies": "Definition two := 2.\nDefinition three : nat := 3.\n"
                               "Example e := 1.\nFixpoint f (n : nat) : nat := n.\n"
                               "Lemma a : True.\nProof. exact I. Qed.\n",
    "definition with a let binder": "Definition d (x := 1) : nat.\nProof.\n  exact x.\nDefined.\n",
    "instances": CLASS + "#[local] Instance i : C := {| c := 1 |}.\n#[local] Instance j : C.\n"
                         "Proof.\n  exact {| c := 0 |}.\nDefined.\n",
    "example": "Example e : 1 = 1.\nProof. reflexivity. Qed.\n",
    "let in a section": "Section S.\nLet l : nat.\nProof.\n  exact 0.\nDefined.\nEnd S.\n",
    "statement over several lines": "Lemma a :\n  (* a comment. with dots. *)\n  True /\\\n"
                                    "  True.\nProof.\n  split; exact I.\nQed.\n",
    "comments around the proof": "Lemma (* c *) a : True. (* hard *)\n(*Proof: trivial.*)\n\n"
                                 "Proof. (* sketch *)\n  exact I. (* done *)\nQed. (* end *)\n"
                                 "Lemma b : True.\nProof. exact I. Qed. (* short *)\n",
    "comment before the closer": "Lemma a : True.\nProof.\n  exact I.\n(* end *) Qed.\n",
    "nested comments and strings in comments":
        '(* outer (* inner. Qed. *) "a string with *) in it" still a comment. *)\n'
        "Lemma a : True.\nProof. exact I. Qed.\n",
    "strings with dots and quotes": 'Lemma a : True.\nProof.\n  idtac "a. (* Qed.";'
                                    ' idtac "say ""hi"". Qed.".\n  exact I.\nQed.\n',
    "qualified names": "Lemma a : Nat.add 0 0 = 0.\nProof. reflexivity. Qed.\n",
    "recursive notation": 'Notation "[[ x ; .. ; y ]]" := (cons x .. (cons y nil) ..).\n'
                          "Lemma a : [[1 ; 2]] = cons 1 (cons 2 nil).\nProof. reflexivity. Qed.\n",
    "keywords inside names": "Definition Lemmas := 1.\nDefinition Proofs := 2.\n"
                             "Definition Qeds := 3.\n",
    "bullets and braces": "Lemma a : True /\\ (True /\\ True).\nProof.\n  split.\n"
                          "  - exact I.\n  - split.\n    + exact I.\n    + { exact I. }\nQed.\n",
    "deep bullets": "Lemma a : True /\\ (True /\\ (True /\\ True)).\nProof.\n  split.\n"
                    "  - exact I.\n  - split.\n    + exact I.\n    + split.\n"
                    "      * exact I.\n      * exact I.\nQed.\n",
    "goal selector with a brace": "Lemma a : True /\\ (True /\\ True).\nProof.\n  split.\n"
                                  "  2: { split.\n       - exact I.\n       - exact I. }\n"
                                  "  exact I.\nQed.\n",
    "closing brace before the closer": "Lemma a : True.\nProof.\n  { exact I. }\nQed.\n",
    "unicode": "(* Comhordú *)\nLemma ú : True.\nProof. exact I. Qed.\n",
    "module": "Module M.\n  Lemma a : True.\n  Proof. exact I. Qed.\n  Lemma b : True.\n"
              "  Proof.\n    exact I.\n  Qed.\nEnd M.\n",
    "ltac mentioning Proof and Qed": 'Ltac t := idtac "Proof. Qed.".\nLemma a : True.\n'
                                     "Proof. t. exact I. Qed.\n",
    "no final newline": "Lemma a : True.\nProof. exact I. Qed.",
}

# Cases that break the layout, with the problems the checker must report: (line, part of the
# message). The cases are valid Rocq, so their sentences can be checked against Rocq's too.
BAD = {
    "no Proof": ("Lemma a : True.\n  exact I.\nQed.\n",
                 [(2, "start the proof with `Proof.`")]),
    "no Proof, proof on the statement's line": ("Lemma a : True. exact I.\nQed.\n",
                                                [(1, "start the proof with `Proof.`")]),
    "no Proof, all on one line": ("Lemma a : True. exact I. Qed.\n",
                                  [(1, "start the proof with `Proof.`")]),
    "no Proof, one-line proof": ("Lemma a : True.\nexact I. Qed.\n",
                                 [(2, "start the proof with `Proof.`")]),
    "no Proof after a multi-line statement": ("Lemma a :\n  True. exact I.\nQed.\n",
                                              [(2, "start the proof with `Proof.`")]),
    "no Proof after a sketch": ("Lemma a : True.\n  (*Proof: trivial.*)\n  exact I.\nQed.\n",
                                [(3, "start the proof with `Proof.`")]),
    "no Proof in a goal": ("Goal True.\n  exact I.\nQed.\n",
                           [(2, "start the proof with `Proof.`")]),
    "no Proof in an instance": (CLASS + "#[local] Instance i : C.\n  exact {| c := 0 |}.\n"
                                        "Defined.\n",
                                [(3, "start the proof with `Proof.`")]),
    "no Proof in a local lemma": ("Local Lemma a : True.\n  exact I.\nQed.\n",
                                  [(2, "start the proof with `Proof.`")]),
    "no Proof after an attribute": ("#[local] Lemma a : True.\n  exact I.\nQed.\n",
                                    [(2, "start the proof with `Proof.`")]),
    "no Proof after a let binder": ("Definition d (x := 1) : nat.\n  exact x.\nDefined.\n",
                                    [(2, "start the proof with `Proof.`")]),
    "Proof on the statement's line": ("Lemma a : True. Proof.\n  exact I.\nQed.\n",
                                      [(1, "put `Proof.` on a new line after the statement")]),
    "Proof after a comment on the statement's line": (
        "Lemma a : True. (* c *) Proof.\n  exact I.\nQed.\n",
        [(1, "put `Proof.` on a new line after the statement")]),
    "one-line proof on the statement's line": (
        "Lemma a : True. Proof. exact I. Qed.\n",
        [(1, "put `Proof.` on a new line after the statement")]),
    "Proof term on the statement's line": ("Lemma a : True. Proof I.\n",
                                           [(1, "put `Proof.` on a new line after the statement")]),
    "tactic after Proof": ("Lemma a : True.\nProof. idtac.\n  exact I.\nQed.\n",
                           [(2, "put nothing after `Proof.` on its line")]),
    "Qed after the last tactic": ("Lemma a : True.\nProof.\n  exact I. Qed.\n",
                                  [(3, "put `Qed.` on a line of its own")]),
    "Qed after the last tactic, with Proof using": (
        "Section S.\nVariable n : nat.\nLemma a : n = n.\nProof using n.\n  reflexivity. Qed.\n"
        "End S.\n",
        [(5, "put `Qed.` on a line of its own")]),
    "Qed after the last tactic, with Proof with": (
        "Lemma a : True.\nProof with auto.\n  idtac... Qed.\n",
        [(3, "put `Qed.` on a line of its own")]),
    "Defined after the last tactic": ("Definition d : nat.\nProof.\n  exact 0. Defined.\n",
                                      [(3, "put `Defined.` on a line of its own")]),
    "Qed after a comment after a tactic": ("Lemma a : True.\nProof.\n  exact I. (* c *) Qed.\n",
                                           [(3, "put `Qed.` on a line of its own")]),
    "Qed after a brace": ("Lemma a : True.\nProof.\n  { exact I. } Qed.\n",
                          [(3, "put `Qed.` on a line of its own")]),
    "Qed after a bullet's tactic": ("Lemma a : True /\\ True.\nProof.\n  split.\n  - exact I.\n"
                                    "  - exact I. Qed.\n",
                                    [(5, "put `Qed.` on a line of its own")]),
    "statement after Qed": ("Lemma a : True.\nProof.\n  exact I.\nQed. Lemma b : True.\n"
                            "Proof.\n  exact I.\nQed.\n",
                            [(4, "put nothing after `Qed.` on its line")]),
    "definition after a one-line proof": ("Lemma a : True.\nProof. exact I. Qed. Definition x := 1.\n",
                                          [(2, "put nothing after `Qed.` on its line")]),
    "one-line proof of 81 characters": (one_liner(81),
                                        [(2, "at most 80 characters, not 81")]),
    "no Proof and Qed after the last tactic": ("Lemma a : True.\n  idtac.\n  exact I. Qed.\n",
                                               [(2, "start the proof with `Proof.`"),
                                                (3, "put `Qed.` on a line of its own")]),
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
    "byte order mark": "\ufeffLemma a : True.\n  exact I.\nQed.\n",
    "unterminated comment": "Lemma a : True.\nProof. exact I. Qed.\n(* no end",
    "unterminated string": 'Lemma a : True.\nProof. idtac "no end',
    "statement with no proof": "Lemma a : True.\n",
    "Proof with no statement": "Proof.\n  exact I.\nQed.\n",
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
