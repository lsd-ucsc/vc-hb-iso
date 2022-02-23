.PHONY: all open clean

all: open

paper.tex: paper.lagda.tex
	agda --latex --latex-dir=. paper.lagda.tex

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
