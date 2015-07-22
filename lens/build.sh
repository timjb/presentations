#!/bin/sh

set -e
pdflatex -output-directory output lens.tex
cp output/lens.pdf .
