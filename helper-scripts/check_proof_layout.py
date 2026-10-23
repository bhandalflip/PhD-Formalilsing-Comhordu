#!/usr/bin/env python3
"""Check that every proof is laid out as `src/AGENTS.md` says.

A proof starts with `Proof.` on a new line after its statement and ends with `Qed.` on a line
of its own. A short proof may instead sit on one line, as `Proof. tac. Qed.`, if that line has
at most 80 characters. Only these line breaks and that length are checked, and nothing else:
not indentation, blank lines, comments, tabs, trailing spaces or line endings.

The script splits each file into sentences exactly as Rocq's lexer does, so no dot or keyword
inside a comment or a string can mislead it.

Usage: python3 helper-scripts/check_proof_layout.py [FILE.v ...]   (from the repository root)

With no files, it checks every .v file in src/ except the vendored src/lib/Extras/. It prints
one line per problem and exits with 1 if there is any.
"""
import bisect
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "src")
VENDORED = os.path.join(SRC, "lib", "Extras")

MAX_ONE_LINE = 80

# The commands that always open a proof, and those that open one only when they have no body.
OPENERS = {"Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Goal"}
OPENERS_WITHOUT_BODY = {"Definition", "Example", "Instance", "Fixpoint", "CoFixpoint", "Let"}
CLOSERS = {"Qed", "Defined", "Admitted", "Abort", "Save"}
MODIFIERS = r"(?:(?:Local|Global|Polymorphic|Monomorphic|Cumulative|NonCumulative)\s+)*"
COMMAND = re.compile(r"\s*" + MODIFIERS + r"([A-Za-z_][\w']*)(?:\s+([A-Za-z_][\w']*))?")
ATTRIBUTE = re.compile(r"#\[[^\]]*\]")

# Rocq's blanks. A dot ends a sentence only if one of these, or the end of the file, follows it.
BLANKS = " \t\n\r"
# A goal selector before a brace, as in `2: {`, which focuses on that goal.
SELECTOR = re.compile(r"(?:\d+|\[\s*[^\]\s]+\s*\])\s*:\s*")


def skip_string(text, i):
    """Return the offset just after the string that starts at text[i], a double quote.
    Rocq reads `""` inside a string as one quote; here it ends one string and starts the next,
    which keeps the same characters inside strings."""
    j = text.find('"', i + 1)
    return len(text) if j < 0 else j + 1


def skip_comment(text, i):
    """Return the offset just after the comment that starts at text[i], an opening `(*`.
    Comments nest, and a string inside a comment hides any `*)` in it, as in Rocq."""
    depth, i = 1, i + 2
    while i < len(text):
        if text.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif text.startswith("*)", i):
            depth, i = depth - 1, i + 2
            if depth == 0:
                return i
        elif text[i] == '"':
            i = skip_string(text, i)
        else:
            i += 1
    return len(text)


def lex(text):
    """Split a Rocq file into sentences, as Rocq's lexer does.

    Returns (sentences, masked): the sentences as (start, end) offsets, and a copy of the text
    with every comment and string blanked out, newlines kept, for reading the sentences' words.
    A sentence ends with a `.` or `...` followed by a blank or the end of the file, but not with
    the token `..`. Between sentences, a run of `-`, `+` or `*` is a bullet and a `{` or `}` is
    a brace, each a sentence of its own, as is a goal selector with its brace, such as `2: {`.
    """
    sentences, masked = [], list(text)
    i, n, start = 0, len(text), None
    if text.startswith("\ufeff"):
        i = 1
    while i < n:
        c = text[i]
        if text.startswith("(*", i):
            j = skip_comment(text, i)
            masked[i:j] = [x if x == "\n" else " " for x in text[i:j]]
            i = j
            continue
        if c == '"':
            if start is None:
                start = i
            j = skip_string(text, i)
            masked[i:j] = [x if x == "\n" else " " for x in text[i:j]]
            i = j
            continue
        if c in BLANKS:
            i += 1
            continue
        if start is None:
            if c in "-+*":
                j = i
                while j < n and text[j] == c:
                    j += 1
                sentences.append((i, j))
                i = j
                continue
            if c in "{}":
                sentences.append((i, i + 1))
                i += 1
                continue
            start = i
        if c == ".":
            if text.startswith("..", i):
                i += 2  # the token `..`; a `...` then ends its sentence with its last dot
                continue
            if i + 1 == n or text[i + 1] in BLANKS:
                sentences.append((start, i + 1))
                start = None
        elif c == "{" and SELECTOR.fullmatch(text[start:i]):
            sentences.append((start, i + 1))
            start = None
        i += 1
    if start is not None:
        sentences.append((start, n))
    return sentences, "".join(masked)


def command(masked, sentence):
    """The command a sentence starts with and the word after it, past any attributes and
    modifiers such as `Local`, or (None, None)."""
    words = ATTRIBUTE.sub(" ", masked[sentence[0]:sentence[1]])
    m = COMMAND.match(words)
    return (m.group(1), m.group(2)) if m else (None, None)


def has_body(masked, sentence):
    """Whether a definition has a body: a `:=` outside any brackets."""
    depth, s = 0, masked[sentence[0]:sentence[1]]
    for i, c in enumerate(s):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0 and s.startswith(":=", i):
            return True
    return False


def opens_proof(masked, sentence):
    keyword, _ = command(masked, sentence)
    return keyword in OPENERS or (keyword in OPENERS_WITHOUT_BODY
                                  and not has_body(masked, sentence))


def proof_start(masked, sentence):
    """For a sentence that starts with `Proof`: "opens" if it opens the proof, as `Proof.`,
    `Proof using …` and `Proof with …` do, or "whole" if it is a whole proof on its own, as
    `Proof term.` is. For any other sentence, None."""
    m = re.match(r"\s*Proof(?![\w'])(.*?)\.?\s*$", masked[sentence[0]:sentence[1]], re.S)
    if not m:
        return None
    rest = m.group(1).split()
    return "opens" if not rest or rest[0] in ("using", "with", "Mode") else "whole"


def proofs(sentences, masked):
    """Yield (k, p, c) for each proof, as indices into sentences: its statement, its first
    sentence and its last, the closer, such as `Qed.`. A statement that another statement or the
    end of the file follows before any closer is skipped: its file doesn't compile."""
    k = 0
    while k < len(sentences):
        if not opens_proof(masked, sentences[k]):
            k += 1
            continue
        p = c = k + 1
        while c < len(sentences):
            if (command(masked, sentences[c])[0] in CLOSERS
                    or (c == p and proof_start(masked, sentences[c]) == "whole")):
                break
            c = len(sentences) if opens_proof(masked, sentences[c]) else c + 1
        if c == len(sentences):
            k = p
            continue
        yield k, p, c
        k = c + 1


def check_text(text):
    """Return the layout problems in a file's text, as (line, message) pairs, lines from 1."""
    sentences, masked = lex(text)
    line_starts = [0] + [m.end() for m in re.finditer("\n", text)]

    def first_line(k):
        return bisect.bisect_right(line_starts, sentences[k][0])

    def last_line(k):
        return bisect.bisect_right(line_starts, sentences[k][1] - 1)

    problems = []
    for k, p, c in proofs(sentences, masked):
        keyword, name = command(masked, sentences[k])
        name = name if keyword != "Goal" and name else keyword
        closer = command(masked, sentences[c])[0]
        closer = closer + "." if closer in CLOSERS else "Proof."
        has_proof = proof_start(masked, sentences[p]) is not None
        one_line = has_proof and first_line(p) == last_line(c)
        if p < c and not has_proof:
            problems.append((first_line(p), f"{name}: start the proof with `Proof.`, on a new line "
                                            "after the statement"))
        elif first_line(p) == last_line(k):
            problems.append((first_line(p), f"{name}: put `Proof.` on a new line after the "
                                            "statement"))
        elif one_line:
            length = len(text[line_starts[first_line(p) - 1]:].split("\n", 1)[0].rstrip())
            if length > MAX_ONE_LINE:
                problems.append((first_line(p), f"{name}: a proof on one line can have at most "
                                                f"{MAX_ONE_LINE} characters, not {length}; spread "
                                                "it over lines"))
        elif p + 1 < c and first_line(p + 1) == last_line(p):
            problems.append((first_line(p), f"{name}: put nothing after `Proof.` on its line"))
        if p < c and first_line(c) == last_line(c - 1) and first_line(p) != last_line(c):
            problems.append((first_line(c), f"{name}: put `{closer}` on a line of its own"))
        if c + 1 < len(sentences) and first_line(c + 1) == last_line(c):
            problems.append((last_line(c), f"{name}: put nothing after `{closer}` on its line"))
    return problems


def default_files():
    files = []
    for dirpath, dirnames, filenames in os.walk(SRC):
        dirnames.sort()
        if dirpath == VENDORED or dirpath.startswith(VENDORED + os.sep):
            continue
        files.extend(os.path.join(dirpath, f) for f in sorted(filenames) if f.endswith(".v"))
    return files


def main(argv):
    files = argv or default_files()
    if not files:
        sys.exit("check_proof_layout.py: no .v files to check")
    count = 0
    for path in files:
        try:
            with open(path, encoding="utf-8", errors="replace", newline="") as f:
                text = f.read()
        except OSError as e:
            sys.exit(f"check_proof_layout.py: {e}")
        shown = os.path.relpath(path)
        for line, message in sorted(check_text(text)):
            print(f"{shown}:{line}: {message}")
            count += 1
    if count:
        print(f"{count} layout problem{'s' if count > 1 else ''}. The rule is in src/AGENTS.md.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
