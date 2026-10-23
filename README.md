# Comhordú in Rocq

This repository holds a proof, checked by the [Rocq prover](https://rocq-prover.org), that the Comhordú coordination protocol is safe. It formalises my PhD thesis, [*Formalising a Real-Time Coordination Model*](doc/thesis/2014-10-28-phd-thesis.pdf) (Trinity College Dublin, 2014).

## History

Comhordú coordinates mobile entities, such as cars, robots or drones, that move in real time and talk over an unreliable wireless network. Each entity is in a mode, and each pair of modes has a minimum distance. Safety means that no two entities are closer than their modes allow. A fail-safe mode needs no distance at all. So the protocol has an entity broadcast a new mode for a set time before entering it. That gives any entity it might threaten the time to switch to a fail-safe mode.

Mélanie Bouroche created Comhordú in [her PhD thesis](https://www.scss.tcd.ie/publications/theses/phd/TCD-SCSS-PHD-2007-07.pdf) in 2007. In mine, I revise it so that it can be made formal. I define a language for such systems, write the protocol in it and prove the protocol safe (Theorem 6.1, p.140). That is, if every entity starts in a fail-safe mode and runs the protocol, every state the system can reach is safe.

I also encoded the language, the protocol and the proof in Coq. The proof was only partly checked, though: its main theorem rested on lower-level results, and many of them were assumed without proof (Summary, p.ii). In 2015, with 254 results still unproved, I wrote [a plan](doc/archive/2015-05-08-coq-project-plan.pdf) to finish it.

In 2026 I finished the proof with AI agents, reviewing every change as it went in. It now runs on Rocq 9.2, and its main theorem, `safety`, rests on no unproved result. Besides the model's parameters and their constraints, it assumes only six axioms from Rocq's standard library, such as classical logic. [A concrete model](src/model/ModelConsistency.v), built without axioms, shows that the constraints can all be met.

Finishing the proof turned up errors in the thesis. The [thesis corrections](doc/thesis/thesis-corrections.md) list them, and the [thesis remarks](doc/thesis/thesis-remarks.md) note other things worth knowing. The Rocq proof also departs from the thesis's in many details. Where they differ, the Rocq proof is the one to trust.

The thesis suggested that its language could be reused for other protocols (p.197). Now it can be. The language takes a protocol's processes as parameters, and its general results sit apart from the protocol, in [`src/lang/`](src/lang/README.md).

## Model your own system

If you want to use Comhordú for a system of your own, build on this formalisation rather than on the thesis alone.

Write your system's model as a value of the class [`ComhModel`](src/model/ComhBasics.v). The model gives your system's modes, which of them are fail-safe, how long each change of mode takes, the message latency, the maximum speed, the minimum distances, and so on. Rocq accepts the value only once you have proved that it meets every constraint of the model. `safety` then holds for your model:

```coq
Require Import ComhCoq.model.ComhBasics ComhCoq.protocol.Main.

Definition my_model : ComhModel := {| (* your system's model *) |}.

Check @safety my_model.
```

[`concrete_model`](src/model/ModelConsistency.v) is a small, complete example.

Then check that your system runs exactly Comhordú's protocol, as [`src/protocol/Protocol.v`](src/protocol/Protocol.v) defines it. `safety` says nothing about a protocol that differs, however slightly. A test oracle, which checks what your system does against what the protocol allows, is one way to check.

A formal refinement, from the protocol down to your system, is another way, but a limited one. The model runs in real time, so any refinement must include a timed semantics. The language's tiers may also make standard refinement techniques hard to apply. Still, refinement is not out of reach: existing techniques could be adapted to it.

## Build and check

You need Rocq 9.2 and its standard library, which [`rocq-comhordu.opam`](rocq-comhordu.opam) lists. To install them with opam, run `opam install . --deps-only` from the root of the repository. On Windows, use WSL.

To use Docker instead, run `make` in the official image, `rocq/rocq-prover:9.2.0`, which is the one CI uses:

```sh
docker run --rm -it -v "$PWD:/work" -w /work --user root -e OPAMROOT=/home/rocq/.opam -e PATH=/home/rocq/.opam/4.14.2+flambda/bin:/usr/local/bin:/usr/bin:/bin rocq/rocq-prover:9.2.0 make
```

If you can use neither, [`helper-scripts/install_rocq.sh`](helper-scripts/README.md) unpacks the same image's Rocq for you.

Then, from the root of the repository:

- `make` checks every proof.
- `make assumptions` lists what `safety` rests on.
- `python3 helper-scripts/check_proof_layout.py`, after `make`, checks how every proof is laid out.
- `make coqdoc` builds web pages of the code in `CoqDoc/`.
- `make clean` removes everything the build made.

CI runs the first three on every pull request.

## Folders

Each folder in `src/` builds only on the ones before it.

- [`src/lib/`](src/lib/README.md): general tools that know nothing about Comhordú.
- [`src/model/`](src/model/README.md): the model, as the class `ComhModel`.
- [`src/lang/`](src/lang/README.md): the language.
- [`src/protocol/`](src/protocol/README.md): the protocol, and the proof of `safety` in `Main.v`.
- [`doc/thesis/`](doc/thesis/README.md): the thesis, with its corrections and remarks.
- [`doc/adr/`](doc/adr): a record of each design decision.
- [`doc/reports/`](doc/reports): reports on the work, such as the first pass at the proofs.
- [`doc/archive/`](doc/archive/README.md): old documents, such as the 2015 plan.
- [`doc/workstreams/`](doc/workstreams): plans for work in progress.
- [`helper-scripts/`](helper-scripts/README.md): scripts that the build does not need.
