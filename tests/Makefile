.PHONY: testbin test

test:
	./build/exec/runtests $(IDRIS2) --timing --interactive --only $(only)

testbin:
	idris2 --build tests.ipkg

clean:
	$(RM) failures
	$(RM) -r build
	$(RM) -r **/**/build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
