default: test

.PHONY: test
test:
	@../../lib/cbmc/regression/test.pl -p -c "../../../src/emu/emu"

.PHONY: show
show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

.PHONY: clean
clean:
	$(RM) tests.log
