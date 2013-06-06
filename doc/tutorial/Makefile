TARGET   = sawScriptTutorial
SRCS     = ${TARGET}.tex ${wildcard *.bib} ${wildcard *.cls} ${wildcard *.sty} figures/sawScriptExecution.pdf
SPELLSRC = ${TARGET}.tex 
NEWSPELL = ${TARGET}.SPELLNEW
OLDSPELL = ${TARGET}.SPELLOLD
SPELL    = aspell -t -l
AUX      = ${wildcard *.blg} ${wildcard *.bbl} ${wildcard *.aux} \
           ${wildcard *.eps} ${wildcard *.log} ${wildcard *.toc} 

all: pdf

pdf: ${TARGET}.pdf

${TARGET}.pdf: ${SRCS} Makefile
	pdflatex ${TARGET}
	bibtex ${TARGET}
	pdflatex ${TARGET}
	pdflatex ${TARGET}

.PHONY: spellClean superClean clean quickSpell

run:
	sawScript ${TARGET}.tex -c ../../Examples/ECC/build -j ../../jdk1.6/classes.jar

clean:
	rm -f ${AUX}

superClean: clean
	rm -f *.dvi *.pdf 

spellClean:
	rm -f ${NEWSPELL} ${OLDSPELL}

quickSpell:
	@touch ${NEWSPELL}
	@mv -f ${NEWSPELL} ${OLDSPELL}
	@cat ${SPELLSRC} | ${SPELL} | tr "A-Z" "a-z" | sort | uniq | less > ${NEWSPELL}
	@echo '(The ones marked with < are new.)'
	@diff ${NEWSPELL} ${OLDSPELL}
