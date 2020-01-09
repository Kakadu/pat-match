VERBOSE=#--verbose
.PHONY: run run-mini
all: run


run:
	dune exec ./main2.exe $(VERBOSE)

run-mini:
	dune exec mini/minirun.exe $(VERBOSE)

clean:
	$(RM) -r _build
