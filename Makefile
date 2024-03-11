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

frontend:
	cd rr_frontend && ./refinedrust build && ./refinedrust install

RUST_SRC = case_studies/minivec stdlib/vec stdlib/option case_studies/paper-examples case_studies/tests

%.gen: % phony
	cd $< && cargo refinedrust
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
builddep/refinedrust-builddep.opam: refinedrust.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@echo "$$BUILDDEP_OPAM_BODY" > $@
	@opam show -f depends: ./refinedrust.opam >> $@
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

config:
	@echo "# Setting default configuration"
	@cp theories/caesium/config/default_config.v theories/caesium/config/selected_config.v
.PHONY: config

config-no-align:
	@echo "# Setting no-align configuration"
	@cp theories/caesium/config/no_align_config.v theories/caesium/config/selected_config.v
.PHONY: config-no-align

# Currently, we don't need to do anything special before building RefinedC in opam.
prepare-install-refinedrust:
	@true
.PHONY: prepare-install-refinedrust
