# Helper scripts

None of these is part of the proof: the Rocq development in [`src/`](../src) builds and checks without them, and nothing they print changes what is proved.

| Script | What it does | Run it with | Also used by |
|---|---|---|---|
| [`summarise_assumptions.py`](summarise_assumptions.py) | Prints, as Markdown, the unproved results that the top-level `safety` theorem still rests on, then how many standard-library axioms it uses. It also counts every `Admitted` and `Conjecture` in `src/`, used by `safety` or not. | `make assumptions`, after `make` | CI, which writes its output to the job summary |
| [`install_rocq.sh`](install_rocq.sh) | Installs Rocq 9.2.0 where there is no Docker daemon and no opam: it downloads the CI image's layers from Docker Hub and unpacks the image's Rocq to `/home/rocq/.opam/4.14.2+flambda`. Does nothing if it's already there. | `helper-scripts/install_rocq.sh`, as root, then `export PATH=/home/rocq/.opam/4.14.2+flambda/bin:$PATH` | Agents in sandboxed sessions, per the top-level `AGENTS.md` |

Run scripts from the repository root, with the same Rocq toolchain as the build (see the [main README](../README.md)).
