VERBOSE=--verbose
all: run 


run: 
	dune exec ./main.exe $(VERBOSE)

clean:
	$(RM) -r _build

