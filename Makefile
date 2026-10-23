# Standard Rocq project Makefile: generates Makefile.coq from _CoqProject via `rocq makefile`
# and delegates every other target to it (e.g. `make html`, `make install`, `make validate`).

# Have Rocq write, beside each file it compiles, where each of the file's sentences starts and
# ends, in a .v.timing file. It costs no build time, and the proof layout check reads them.
export TIMING ?= 1

all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d
	@rm -rf CoqDoc

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

# Remaining assumptions under the top-level `safety` theorem, as a Markdown summary.
assumptions: all
	python3 helper-scripts/summarise_assumptions.py

# Pretty-printed docs: CoqDoc/verbose (with proofs) and CoqDoc/light (proofs hidden).
coqdoc:
	mkdir -p CoqDoc/light CoqDoc/verbose
	rocq doc --html -R src ComhCoq -d CoqDoc/verbose src/*/*.v --no-index --toc
	rocq doc --html -g -R src ComhCoq -d CoqDoc/light src/*/*.v --no-index --toc

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean assumptions coqdoc force
