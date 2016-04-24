#!/usr/bin/env sh

set -e
mkdir -p output
pdflatex -shell-escape -output-directory output slides.tex
cp output/slides.pdf .