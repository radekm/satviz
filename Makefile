# Copyright (c) 2013 Radek Micek

IDRIS = idris
RUNHASKELL = runhaskell

.PHONY: default test d3-samples clean

default:
	@echo "Please select a target"

satviz:
	$(IDRIS) --target javascript -i src -o src/SatvizRaw.js \
	    src/Main.idr
	$(RUNHASKELL) OptApplyEval.hs src/SatvizRaw.js src/Satviz.js

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
	$(IDRIS) --target javascript -i src -o d3-samples/ForceLayout.js \
	    d3-samples/ForceLayout.idr

clean:
	rm -f src/*.ibc
	rm -f src/SatvizRaw.js src/Satviz.js
	rm -f test/*.ibc
	rm -f d3-samples/*.ibc
	rm -f d3-samples/*.js
