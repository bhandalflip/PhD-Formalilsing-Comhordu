# Helper scripts

None of these is part of the proof: the Rocq development in [`src/`](../src) builds and checks without them, and nothing they print changes what is proved.

| Script | What it does | Run it with | Also used by |
|---|---|---|---|
| [`summarise_assumptions.py`](summarise_assumptions.py) | Prints, as Markdown, the unproved results that the top-level `safety` theorem still rests on, then how many standard-library axioms it uses. It also counts every `Admitted` and `Conjecture` in `src/`, used by `safety` or not. | `make assumptions`, after `make` | CI, which writes its output to the job summary |
| [`check_proof_layout.py`](check_proof_layout.py) | Checks that every proof in `src/` is laid out as [`src/AGENTS.md`](../src/AGENTS.md) says, and prints each problem with its file, its line and the fix. It reads the sentences that Rocq found in each file during `make`, and checks only line breaks and the length of one-line proofs. | `python3 helper-scripts/check_proof_layout.py`, after `make` | CI, after the build, which fails on any problem |
| [`test_check_proof_layout.py`](test_check_proof_layout.py) | Tests `check_proof_layout.py` on the corners of Rocq's syntax and of the layout. Rocq compiles every case, so it needs `rocq` on the `PATH`. | `python3 helper-scripts/test_check_proof_layout.py` | CI, before it runs the checker |
| [`install_rocq.sh`](install_rocq.sh) | Installs Rocq 9.2.0 where there is no Docker daemon and no opam: it downloads the CI image's layers from Docker Hub and unpacks the image's Rocq to `/home/rocq/.opam/4.14.2+flambda`. Does nothing if it's already there. | `helper-scripts/install_rocq.sh`, as root, then `export PATH=/home/rocq/.opam/4.14.2+flambda/bin:$PATH` | Agents in sandboxed sessions, per the top-level `AGENTS.md` |

Run scripts from the repository root, with the same Rocq toolchain as the build (see the [main README](../README.md)).
