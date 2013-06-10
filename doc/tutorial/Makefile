TARGET   = sawScriptTutorial
SRCS     = ${TARGET}.md ${wildcard *.bib} ${wildcard *.cls} ${wildcard *.sty} figures/sawScriptExecution.pdf
SPELLSRC = ${TARGET}.tex 
NEWSPELL = ${TARGET}.SPELLNEW
OLDSPELL = ${TARGET}.SPELLOLD
SPELL    = aspell -t -l
AUX      = ${wildcard *.blg} ${wildcard *.bbl} ${wildcard *.aux} \
           ${wildcard *.eps} ${wildcard *.log} ${wildcard *.toc} 
PDFARGS   = -H tutorial-head.tex \
            -B tutorial-before.tex \
            -A tutorial-after.tex \
	    -V documentclass:galois-whitepaper \
	    -V fontsize:12 \
            --latex-engine=xelatex
HTMLARGS  = --css doc.css \
            -B tutorial-before.html \
            --standalone \
            --self-contained

all: pdf

pdf: ${TARGET}.pdf ${TARGET}.html

${TARGET}.pdf: ${SRCS} Makefile
	pandoc ${PDFARGS} -o $@ ${TARGET}.md

${TARGET}.html: ${SRCS} Makefile
	pandoc ${HTMLARGS} -o $@ ${TARGET}.md

.PHONY: spellClean superClean clean quickSpell

#run:
#	sawScript ${TARGET}.tex -c ../../Examples/ECC/build -j ../../jdk1.6/classes.jar

clean:
	rm -f ${AUX}

superClean: clean
	rm -f ${TARGET}.pdf ${TARGET}.html

spellClean:
	rm -f ${NEWSPELL} ${OLDSPELL}

quickSpell:
	@touch ${NEWSPELL}
	@mv -f ${NEWSPELL} ${OLDSPELL}
	@cat ${SPELLSRC} | ${SPELL} | tr "A-Z" "a-z" | sort | uniq | less > ${NEWSPELL}
	@echo '(The ones marked with < are new.)'
	@diff ${NEWSPELL} ${OLDSPELL}
