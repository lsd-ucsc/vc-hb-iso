POSTPROCESS := postprocess-latex.pl

.PHONY: all open clean

all: open

paper.tex: paper.lagda.tex
	agda --latex --latex-dir=. paper.lagda.tex
	cp $(shell agda --print-agda-dir)/latex/$(POSTPROCESS) .
	perl $(POSTPROCESS) paper.tex > paper.processed
	mv paper.processed paper.tex

paper.pdf: paper.tex
	xelatex paper.tex
	bibtex paper
	xelatex paper.tex
	bibtex paper
	xelatex paper.tex
	bibtex paper

open: paper.pdf
	open paper.pdf

clean:
	rm -f *.out *.aux *.log *.bbl *.blg paper.tex
