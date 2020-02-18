VERBOSE=#--verbose
.PHONY: run run-mini celan

all: guards


run:
	dune exec ./main2.exe $(VERBOSE)

gadt:
	dune exec ./main_gadt.exe $(VERBOSE)

guards:
	dune exec ./main_guards.exe $(VERBOSE)

run-mini:
	dune exec mini/minirun.exe $(VERBOSE)

celan: clean
clean:
	$(RM) -r _build
