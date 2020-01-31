VERBOSE=#--verbose
.PHONY: run run-mini celan

all: gadt


run:
	dune exec ./main2.exe $(VERBOSE)

gadt:
	dune exec ./main_gadt.exe $(VERBOSE)

run-mini:
	dune exec mini/minirun.exe $(VERBOSE)

celan: clean
clean:
	$(RM) -r _build
