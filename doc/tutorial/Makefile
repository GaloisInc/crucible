TARGET   = tutorial
SRCS     = ${TARGET}.md ${wildcard *.bib} ${wildcard *.cls} ${wildcard *.sty} figures/sawScriptExecution.pdf
CODE     = ${wildcard code/*.c} \
           ${wildcard code/*.cry} \
           ${wildcard code/*.java} \
           ${wildcard code/*.saw}
SPELLSRC = ${TARGET}.tex 
NEWSPELL = ${TARGET}.SPELLNEW
OLDSPELL = ${TARGET}.SPELLOLD
SPELL    = aspell -t -l
AUX      = ${wildcard *.blg} ${wildcard *.bbl} ${wildcard *.aux} \
           ${wildcard *.eps} ${wildcard *.log} ${wildcard *.toc} \
	   sawScriptTutorial.md
PDFARGS   = -H tutorial-head.tex \
            -B tutorial-before.tex \
            -A tutorial-after.tex \
	    --toc \
	    --listings \
	    -V documentclass:galois-whitepaper \
	    -V fontsize:12 \
            --latex-engine=pdflatex
HTMLARGS  = --css doc.css \
            -B tutorial-before.html \
	    --toc \
            --standalone \
            --self-contained

all: pdf

pdf: ${TARGET}.pdf ${TARGET}.html

${TARGET}.pdf: ${SRCS} Makefile
	pandoc ${PDFARGS} -o $@ ${TARGET}.md

${TARGET}.html: ${SRCS} Makefile
	pandoc ${HTMLARGS} -o $@ ${TARGET}.md

# Pre-processing step. Right now, does nothing.
${TARGET}.md: tutorial.md docode.hs ${CODE}
	runhaskell docode.hs < $< > $@

docode: ${TARGET}.md

.PHONY: spellClean superClean clean quickSpell

#run:
#	sawScript ${TARGET}.tex -c ../../Examples/ECC/build -j ../../jdk1.6/classes.jar

clean:
	rm -f ${AUX}

superClean: clean
	rm -f ${TARGET}.pdf ${TARGET}.html ${TARGET}.md

spellClean:
	rm -f ${NEWSPELL} ${OLDSPELL}

quickSpell:
	@touch ${NEWSPELL}
	@mv -f ${NEWSPELL} ${OLDSPELL}
	@cat ${SPELLSRC} | ${SPELL} | tr "A-Z" "a-z" | sort | uniq | less > ${NEWSPELL}
	@echo '(The ones marked with < are new.)'
	@diff ${NEWSPELL} ${OLDSPELL}
