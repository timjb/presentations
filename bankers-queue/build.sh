#!/bin/sh

set -e
pdflatex -shell-escape -output-directory output bankers-queue.tex
cp output/bankers-queue.pdf .
