default: test

DIRS = oracle-solver \
       # Empty last line

# Run all test directories in sequence
.PHONY: test
test:
	@for dir in $(DIRS); do \
		$(MAKE) "$$dir" || exit 1 ; \
	done;

# Pattern to execute a single test suite directory
.PHONY: $(DIRS)
$(DIRS):
	@echo "Running $@..." ;
	$(MAKE) -C "$@" test
