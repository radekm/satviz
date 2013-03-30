# Copyright (c) 2013 Radek Micek

IDRIS = idris

.PHONY: default test d3-samples clean

default:
	@echo "Please select a target"

satviz:
	$(IDRIS) --target javascript -i src -o src/Satviz.js \
	    src/Main.idr

test:
	$(IDRIS) --check -i src test/TestSolver.idr

d3-samples:
	$(IDRIS) --target javascript -i src -o d3-samples/Array.js \
	    d3-samples/Array.idr
	$(IDRIS) --target javascript -i src -o d3-samples/Selection.js \
	    d3-samples/Selection.idr
	$(IDRIS) --target javascript -i src -o d3-samples/Binding.js \
	    d3-samples/Binding.idr
	$(IDRIS) --target javascript -i src -o d3-samples/BindingByKey.js \
	    d3-samples/BindingByKey.idr
	$(IDRIS) --target javascript -i src -o d3-samples/Prompt.js \
	    d3-samples/Prompt.idr

clean:
	rm -f src/*.ibc
	rm -f src/Satviz.js
	rm -f test/*.ibc
	rm -f d3-samples/*.ibc
	rm -f d3-samples/*.js
