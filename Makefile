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

# Currently, we don't need to do anything special before building RefinedC in opam.
prepare-install-refinedrust:
	@true
.PHONY: prepare-install-refinedrust
