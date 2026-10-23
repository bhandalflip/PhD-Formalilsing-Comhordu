#!/usr/bin/env python3
"""Check that every proof is laid out as `src/AGENTS.md` says.

A proof starts with `Proof.` on a new line after its statement and ends with `Qed.` on a line
of its own. A short proof may instead sit on one line, as `Proof. tac. Qed.`, if that line has
at most 80 characters. Only these line breaks and that length are checked, and nothing else:
not indentation, blank lines, comments, tabs, trailing spaces or line endings.

Rocq itself splits each file into sentences. When `make` compiles a file, Rocq writes where
each of its sentences starts and ends to a `.v.timing` file beside it, and this script reads
those, so it can't disagree with Rocq about where a sentence ends. It reads only the first
words of each sentence, to tell a statement, `Proof` or `Qed` from the rest.

Usage: python3 helper-scripts/check_proof_layout.py [FILE.v ...]   (from the repository root,
after `make`)

With no files, it checks every file that `_CoqProject` builds, except the vendored ones in
src/lib/Extras/. It prints one line per problem and exits with 1 if there is any, or with 2 if
Rocq's sentences for a file are missing or older than the file.
"""
import bisect
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJECT = os.path.join(ROOT, "_CoqProject")
VENDORED = os.path.join(ROOT, "src", "lib", "Extras")

MAX_ONE_LINE = 80

# The commands that always open a proof, and those that open one only when they have no body.
OPENERS = {"Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Goal"}
OPENERS_WITHOUT_BODY = {"Definition", "Example", "Instance", "Fixpoint", "CoFixpoint", "Let"}
CLOSERS = {"Qed", "Defined", "Admitted", "Abort", "Save"}
MODIFIERS = r"(?:(?:Local|Global|Polymorphic|Monomorphic|Cumulative|NonCumulative)\s+)*"
COMMAND = re.compile(r"\s*" + MODIFIERS + r"([A-Za-z_][\w']*)(?:\s+([A-Za-z_][\w']*))?")
ATTRIBUTE = re.compile(r"#\[[^\]]*\]")
# One line of Rocq's timing output: a sentence's start and end, as byte offsets in the file.
CHARS = re.compile(r"^Chars (\d+) - (\d+) \[", re.M)


class NoSentences(Exception):
    """Rocq's sentences for a file are missing or older than the file."""


def rocq_sentences(path, text):
    """The sentences of the file at path, whose text is text, as (start, end) character offsets:
    where Rocq found each one when `make` last compiled the file."""
    timing = path + ".timing"
    try:
        stale = os.path.getmtime(timing) < os.path.getmtime(path)
        with open(timing, encoding="utf-8", errors="replace") as f:
            spans = [(int(a), int(b)) for a, b in CHARS.findall(f.read())]
    except OSError:
        raise NoSentences(f"Rocq's sentences for {path} are missing: run `make`, after "
                          "`make clean` if the build is up to date") from None
    if stale:
        raise NoSentences(f"Rocq's sentences for {path} are older than the file: run `make`")
    if not spans and blank_out(text).strip():
        raise NoSentences(f"{timing} names no sentence: has the format of Rocq's timing output "
                          "changed?")
    char_at = {}  # Rocq counts bytes
    offset = 0
    for i, ch in enumerate(text):
        char_at[offset] = i
        offset += len(ch.encode("utf-8"))
    char_at[offset] = len(text)
    try:
        return [(char_at[a], char_at[b]) for a, b in spans]
    except KeyError:
        raise NoSentences(f"{timing} doesn't match {path}: run `make`") from None


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


def blank_out(text):
    """The text with every comment and string replaced by spaces, so that no word inside one is
    read as a command."""
    out, i = list(text), 0
    while i < len(text):
        if text.startswith("(*", i):
            j = skip_comment(text, i)
        elif text[i] == '"':
            j = skip_string(text, i)
        else:
            i += 1
            continue
        out[i:j] = " " * (j - i)
        i = j
    return "".join(out)


def command(words):
    """The command that a sentence's words start with and the word after it, past any
    attributes and modifiers such as `Local`, or (None, None)."""
    m = COMMAND.match(ATTRIBUTE.sub(" ", words))
    return (m.group(1), m.group(2)) if m else (None, None)


def has_body(words):
    """Whether a definition has a body: a `:=` outside any brackets."""
    depth = 0
    for i, c in enumerate(words):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0 and words.startswith(":=", i):
            return True
    return False


def opens_proof(words):
    keyword, _ = command(words)
    return keyword in OPENERS or (keyword in OPENERS_WITHOUT_BODY and not has_body(words))


def proof_start(words):
    """For a sentence that starts with `Proof`: "opens" if it opens the proof, as `Proof.`,
    `Proof using …` and `Proof with …` do, or "whole" if it is a whole proof on its own, as
    `Proof term.` is. For any other sentence, None."""
    m = re.match(r"\s*Proof(?![\w'])(.*?)\.?\s*$", words, re.S)
    if not m:
        return None
    rest = m.group(1).split()
    return "opens" if not rest or rest[0] in ("using", "with", "Mode") else "whole"


def proofs(words):
    """Yield (k, p, c) for each proof, as indices into the sentences, given their words: its
    statement, its first sentence and its last, the closer, such as `Qed.`. A statement that
    another statement or the end of the file follows before any closer is skipped."""
    k = 0
    while k < len(words):
        if not opens_proof(words[k]):
            k += 1
            continue
        p = c = k + 1
        while c < len(words):
            if command(words[c])[0] in CLOSERS or (c == p and proof_start(words[c]) == "whole"):
                break
            c = len(words) if opens_proof(words[c]) else c + 1
        if c == len(words):
            k = p
            continue
        yield k, p, c
        k = c + 1


def check_text(text, sentences):
    """Return the layout problems in a file's text, given its sentences as Rocq found them, as
    (line, message) pairs, lines from 1."""
    words = [blank_out(text[s:e]) for s, e in sentences]
    line_starts = [0] + [m.end() for m in re.finditer("\n", text)]

    def first_line(k):
        return bisect.bisect_right(line_starts, sentences[k][0])

    def last_line(k):
        return bisect.bisect_right(line_starts, sentences[k][1] - 1)

    problems = []
    for k, p, c in proofs(words):
        keyword, name = command(words[k])
        name = name if keyword != "Goal" and name else keyword
        closer = command(words[c])[0]
        closer = closer + "." if closer in CLOSERS else "Proof."
        has_proof = proof_start(words[p]) is not None
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
    """The files that `_CoqProject` builds, except the vendored ones."""
    files = []
    with open(PROJECT, encoding="utf-8") as f:
        for line in f:
            name = line.strip()
            path = os.path.join(ROOT, name)
            if name.endswith(".v") and not path.startswith(VENDORED + os.sep):
                files.append(path)
    return files


def main(argv):
    files = argv or default_files()
    if not files:
        sys.exit("check_proof_layout.py: no .v files to check")
    count, missing = 0, []
    for path in files:
        try:
            with open(path, encoding="utf-8", errors="replace", newline="") as f:
                text = f.read()
        except OSError as e:
            sys.exit(f"check_proof_layout.py: {e}")
        try:
            sentences = rocq_sentences(path, text)
        except NoSentences as e:
            missing.append(str(e))
            continue
        shown = os.path.relpath(path)
        for line, message in sorted(check_text(text, sentences)):
            print(f"{shown}:{line}: {message}")
            count += 1
    for message in missing:
        print(f"check_proof_layout.py: {message}", file=sys.stderr)
    if count:
        print(f"{count} layout problem{'s' if count > 1 else ''}. The rule is in src/AGENTS.md.")
    return 2 if missing else 1 if count else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
