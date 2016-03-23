TARGET   = java-llvm
SRCS     = ${TARGET}.md ${wildcard *.bib} ${wildcard *.cls} ${wildcard *.sty}
CODE     = ${wildcard code/*.c} \
           ${wildcard code/*.cry} \
           ${wildcard code/*.java} \
           ${wildcard code/*.saw}
AUX      = ${wildcard *.blg} ${wildcard *.bbl} ${wildcard *.aux} \
           ${wildcard *.eps} ${wildcard *.log} ${wildcard *.toc}
PDFARGS   = -H head.tex \
            -B before.tex \
            --listings \
            -V documentclass:galois-whitepaper \
            -V fontsize:12 \
            --latex-engine=pdflatex
HTMLARGS  = --css doc.css \
            -B before.html \
            --standalone \
            --self-contained

all: pdf

pdf: ${TARGET}.pdf

${TARGET}.pdf: ${TARGET}.md Makefile galois-whitepaper.cls
	pandoc ${PDFARGS} -o $@ ${TARGET}.md

${TARGET}.html: ${TARGET}.md Makefile
	pandoc ${HTMLARGS} -o $@ ${TARGET}.md

clean:
	rm -f ${AUX}

superClean: clean
	rm -f ${TARGET}.pdf ${TARGET}.html
