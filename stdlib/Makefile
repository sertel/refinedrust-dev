STDLIB = alloc option result spin vec 

%.gen: % phony
	cd $< && cargo refinedrust
.PHONY: phony

%.clean: % phony
	cd $< && cargo clean
.PHONY: phony

generate_stdlib: $(addsuffix .gen, $(STDLIB))

clean_stdlib: $(addsuffix .clean, $(STDLIB))

stdlib: generate_stdlib
	dune build --display short
