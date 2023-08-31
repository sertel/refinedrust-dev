all:
	@dune build _build/default/refinedrust.install --display short
.PHONY: all

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

clean:
	@dune clean
.PHONY: clean

frontend-setup:
	cd rr_frontend && ./rustup-toolchain

frontend: frontend-setup
	cd rr_frontend && ./refinedrust build

#RUST_SRC = $(wildcard rr_frontend/examples/*.rs)
RUST_SRC = rr_frontend/examples/paper.rs

%.rs.gen: %.rs phony
	cd rr_frontend && ./refinedrust run ../$<
.PHONY: phony

generate_all: $(addsuffix .gen, $(RUST_SRC))
.PHONY: generate_all

check_generate_all: generate_all
	git diff --exit-code
.PHONY: check_generate_all

all_with_examples: frontend generate_all
	dune build --display short

builddep-opamfiles: builddep/refinedrust-builddep.opam
	@true
.PHONY: builddep-opamfiles

# see https://stackoverflow.com/a/649462 for defining multiline strings in Makefiles
define BUILDDEP_OPAM_BODY
opam-version: "2.0"
name: "refinedrust-builddep"
maintainer: "Lennard Gäher"
author: "Lennard Gäher"
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
builddep/refinedrust-builddep.opam: refinedrust.opam coq-lithium.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@echo "$$BUILDDEP_OPAM_BODY" > $@
	@opam show -f depends: ./coq-lithium.opam >> $@
	@opam show -f depends: ./refinedrust.opam | sed 's/"coq-lithium".*//g' >> $@
	@echo "]" >> $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of RefinedRust are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedRust package itself (which takes time).
builddep: builddep/refinedrust-builddep.opam
	@echo "# Installing package $^."
	@opam install $(OPAMFLAGS) $^
.PHONY: builddep

DUNE_FILES = $(shell find theories/ -type f -name 'dune')
