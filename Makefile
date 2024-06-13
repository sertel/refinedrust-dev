COQ_PATH =	_build/lib/coq/user-contrib
RUST_TARGET = $(shell rustc -vV | sed -n 's|host: ||p')
RUST_PATH =	target/$(RUST_TARGET)/release

CASE_STUDIES = case_studies/paper_examples case_studies/tests case_studies/minivec case_studies/evenint

### Project setup
setup-nix:
	rm -f dune-project
.PHONY: setup-nix

setup-dune:
	echo "(lang dune 3.8)" > dune-project
.PHONY: setup-dune

### generic build targets
generate_all: generate_stdlib generate_case_studies
.PHONY: generate_all

clean: clean_case_studies clean_stdlib
	@dune clean
.PHONY: clean

all_with_examples: all case_studies.proof
	dune build --display short
.PHONY: all_with_examples

### core components
typesystem:
	cd theories && dune build --display short
.PHONY: typesystem

frontend:
	cd rr_frontend && ./refinedrust build
.PHONY: frontend

all: frontend typesystem stdlib.proof
.PHONY: all

### case studies
case_studies.proof: typesystem generate_case_studies
	cd case_studies && dune build --display short
.PHONY: case_studies.proof

clean_case_studies: $(CASE_STUDIES:=.clean)
.PHONY: clean_case_studies

generate_case_studies:
generate_case_studies: $(CASE_STUDIES:=.crate)
.PHONY: generate_case_studies

case_studies/%.proof:	stdlib.proof case_studies/%.crate
	cd case_studies/$* && dune build --display short

### stdlib
stdlib.proof: typesystem generate_stdlib
	RUST_PATH=$(RUST_PATH) $(MAKE) -C stdlib stdlib.proof
.PHONY: stdlib.proof

clean_stdlib:
	RUST_PATH=$(RUST_PATH) $(MAKE) -C stdlib clean_stdlib
.PHONY: clean_stdlib

generate_stdlib:
	RUST_PATH=$(RUST_PATH) $(MAKE) -C stdlib generate_stdlib
.PHONY: generate_stdlib

### Calling the frontend
# this adds the path to the built frontend so cargo can find it
%.crate:	export PATH := $(CURDIR)/rr_frontend/$(RUST_PATH):$(PATH)
%.crate: %
	cd $* && cargo refinedrust

%.clean: phony
	cd $* && cargo clean
.PHONY: phony

### Builddep handling
# see https://stackoverflow.com/a/649462 for defining multiline strings in Makefiles
define BUILDDEP_OPAM_BODY
opam-version: "2.0"
name: "refinedrust-builddep"
maintainer: "RefinedRust contributors"
author: "RefinedRust contributors"
homepage: "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev"
bug-reports: "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev"
synopsis: "---"
description: """
---
"""
license: "BSD-3-Clause"
depends: [
endef
export BUILDDEP_OPAM_BODY

# Create a virtual Opam package with the same deps as RefinedC, but no
# build.
builddep/refinedrust-builddep.opam: theories/refinedrust.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@echo "$$BUILDDEP_OPAM_BODY" > $@
	@opam show -f depends: ./theories/refinedrust.opam >> $@
	@echo "]" >> $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of RefinedRust are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedRust package itself (which takes time).
builddep: builddep/refinedrust-builddep.opam
	@echo "# Installing package $^."
	@opam install $(OPAMFLAGS) $^
.PHONY: builddep


### Generating _CoqProject
define COQPROJECT_BASE_BODY
# RefinedRust core
-Q _build/default/theories/lithium lithium
-Q _build/default/theories/caesium caesium
-Q _build/default/theories/rust_typing refinedrust

-Q _build/default/case_studies/extra_proofs refinedrust.extra_proofs
endef
export COQPROJECT_BASE_BODY

coqproject-base:
	@echo "$$COQPROJECT_BASE_BODY" > _CoqProject

case_studies/%.coqproject: coqproject-base
	@echo "-Q _build/default/case_studies/$*/output/$* refinedrust.examples.$*" >> _CoqProject

coqproject-case-studies: $(CASE_STUDIES:=.coqproject)

coqproject: coqproject-base coqproject-case-studies

