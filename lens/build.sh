#!/bin/sh

set -e
pdflatex -shell-escape -output-directory output lens.tex
cp output/lens.pdf .
