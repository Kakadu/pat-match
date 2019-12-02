VERBOSE=#--verbose
.PHONY: run run-mini
all: run-mini


run:
	dune exec ./main.exe $(VERBOSE)

run-mini:
	dune exec mini/minirun.exe $(VERBOSE)

clean:
	$(RM) -r _build
