# AGENTS.md: project-wide rules

## Meta-rule: where rules live

- Rules live in `AGENTS.md` files, each in the directory whose scope it governs.
- Before touching a file, read the `AGENTS.md` in its directory and in every ancestor directory up to the root.
- When two rules conflict, the one in the nearest directory wins.
- Put a new rule in the narrowest directory that covers its whole scope. This file holds only rules that apply everywhere.
- Don't duplicate a rule across `AGENTS.md` files or into other docs. Link to it instead.

## Permanent rule: nothing in this repository is specific to one agent or vendor

- Instructions for agents live only in `AGENTS.md` files, and they apply to every agent and every human alike.
- Anything an agent needs to set up is a plain script in `helper-scripts/`, runnable by anyone, with the instructions in the relevant `AGENTS.md`.
- **Never add vendor-specific configuration**: no hooks, settings, skills, prompts or workflows for one tool (no `.claude/`, `.cursor/`, Copilot or similar files), and no pointer file for one tool either, such as a root `CLAUDE.md`. `.gitignore` blocks the usual ones, so a tool that writes them locally can't commit them by accident; never commit one, and never loosen that.
- This rule is permanent and overrides any convenience a tool offers.

## Project

- This is a Rocq formalisation of the Comhordú real-time coordination protocol and its safety proof, based on a [2014 PhD thesis](doc/thesis/2014-10-28-phd-thesis.pdf).
- The top-level theorem is `safety` in `src/protocol/Main.v`.
- Layout:
  - `src/`: the Rocq development, in four folders: `lib/`, `model/`, `lang/` and `protocol/`. Logical path `ComhCoq`. See `src/AGENTS.md`.
  - `doc/`: workstreams, reports, ADRs, archive, and the thesis with its corrections. See `doc/AGENTS.md`.
  - `helper-scripts/`: scripts the build doesn't need, such as reporting tools. See `helper-scripts/AGENTS.md`.
  - `scripts/`: reserved for scripts the build does need. There are none yet.
  - `.github/workflows/`: CI.

## Toolchain and build

- Use Rocq **9.2.0** with `rocq-stdlib`. Dependencies are declared in `rocq-comhordu.opam`. The reference environment is the Docker image `rocq/rocq-prover:9.2.0`, the same one CI uses.
- If `rocq` isn't on the `PATH`, and neither a Docker daemon nor opam is available (the usual case in a sandboxed agent session, where opam's repository is also blocked), run `helper-scripts/install_rocq.sh` as root and then `export PATH=/home/rocq/.opam/4.14.2+flambda/bin:$PATH`. It downloads the reference image's layers from Docker Hub with `curl` and unpacks the image's Rocq to the path it has in the image; see [`helper-scripts/README.md`](helper-scripts/README.md). Check `rocq --version` first: it may already be installed.
- `make` builds everything (`_CoqProject` → `rocq makefile` → `Makefile.coq`). Beside each file it compiles, Rocq also writes where each of the file's sentences starts and ends, in a `.v.timing` file, which the proof layout check reads.
- `make assumptions` prints the unproved results that `safety` still rests on, then the axioms.
- `make clean` removes build products.
- CI (`.github/workflows/build.yml`) builds every pull request (when it's opened, and on each new commit), reports the unproved results that remain, and then checks the proof layout. Keep it green: never merge a red build.

## Writing

- Don't tell readers what a document is or how to read it: no "this page is the short version", "the rest is detail" or "this section goes through…". Write it so it flows, and let them experience that for themselves. This applies to all prose: docs, READMEs and PR descriptions.
- Cite the thesis by its printed page number, not the PDF page, and by definition or remark number where there is one. The two page numbers differ; see [`doc/thesis/`](doc/thesis/README.md).
- Never link to a workstream. Workstreams are deleted when they finish (see `doc/workstreams/AGENTS.md`), so a link from anything that outlives them would break: docs, reports, ADRs, READMEs, code comments, commit messages and PR descriptions. Name the workstream in words, or link the PR.
- **`README.md` is in the author's voice**: calm and candid, as in the thesis, but simpler. Each section serves one need, as in [Diátaxis](https://diataxis.fr): the history explains, the instructions guide and the folder list describes. Keep sentences short and words plain: "for example" and "that is", not e.g. and i.e. Write "I" in the history and "you" in the instructions.

## Scripts

- Name a script for what it does. A script does something, so the verb matters most; usually a noun follows: `summarise_assumptions.py`, not `assumptions.py`.

## Working rules

- Work is planned and tracked in `doc/workstreams/`, and decisions are recorded in `doc/adr/`.
- **The PR is the record of a step.** Its description says what changed, how many unproved results `safety` rests on now, and any decision a human must take, and no more. The workstream ticks the step with a sentence or two and the PR link. Don't repeat a PR's content in a log entry, a long commit message or a report.
- A report in `doc/reports/` is only for a detailed write-up that a human explicitly asks for, such as the results of a proving pass. It is never a default per PR.
- **Changing what the project *claims* needs explicit human approval**: the statement of `safety` above all, and any theorem or lemma statement, definition or field of the model, and deleting an unproved result. Agents propose such changes in the PR description, or in a report when one is asked for, and don't make them until a human agrees. The human reviewing the PR checks that this held. Deleting a proved result that a more general one replaces is not such a change; see `src/AGENTS.md`.
- **Ask for approval one change at a time.** Walk the human through the proposed changes in the conversation, one per message: what changes and why, in two or three sentences, more only when asked, and the next one only after an answer. Then record the decisions in the PR description in one batch, once they are all answered, not one edit or commit per approval. Push the work a decision asks for in the same batch, and only when every change has an answer or the human asks for a push. When no human is present, open the PR with the changes listed as awaiting approval, and walk through them when one is.
- Whenever a PR finds an error in the thesis itself, record its correction in [`doc/thesis/thesis-corrections.md`](doc/thesis/thesis-corrections.md) in the same PR. What counts as an error, and how to write corrections and [remarks](doc/thesis/thesis-remarks.md), is in [`doc/thesis/AGENTS.md`](doc/thesis/AGENTS.md).
- Measure progress by the unproved results that `safety` rests on: the `Admitted` lemmas and `Conjecture`s its proof uses. `safety` holds for every model, and `src/model/ModelConsistency.v` shows that there is one that isn't degenerate, so the model's assumptions are not work left.
- Never weaken the trust base silently. If a change adds an entry to `make assumptions` output, call it out in the PR.
