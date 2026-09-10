PDFLATEX = /Library/TeX/texbin/pdflatex
BIBTEX = /Library/TeX/texbin/bibtex

all: main.pdf

main.pdf: main.tex macros.tex titlepage.tex references.bib chapters/*.tex
	PATH="$(PATH):/Library/TeX/texbin" $(PDFLATEX) -interaction=nonstopmode main.tex || true
	PATH="$(PATH):/Library/TeX/texbin" $(BIBTEX) main || true
	PATH="$(PATH):/Library/TeX/texbin" $(PDFLATEX) -interaction=nonstopmode main.tex || true
	PATH="$(PATH):/Library/TeX/texbin" $(PDFLATEX) -interaction=nonstopmode main.tex || true

clean:
	rm -f *.aux *.log *.toc *.out *.fls *.fdb_latexmk *.bbl *.blg chapters/*.aux main.pdf

.PHONY: all clean
