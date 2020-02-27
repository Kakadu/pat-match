OUT=pat-match
.PHONY: $(OUT).pdf clean celan

all: $(OUT).pdf

FILES_TEX=$(OUT).tex evaluation.tex conclusion.tex demo.tex \
	examples.tex goals.tex injection.tex introduction.tex \
	polymorphic-unification.tex reification.tex

$(OUT).pdf: $(FILES_TEX)
	pdflatex $<
	bibtex $(OUT).aux
	pdflatex $<
	pdflatex $<

celan: clean
clean:
	$(RM) *.bak *.out

