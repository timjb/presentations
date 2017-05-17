#!/bin/sh

set -e
mkdir -p output
if pdflatex -shell-escape -interaction=nonstopmode -output-directory output theoreme-fuer-lau.tex; then
  cp output/theoreme-fuer-lau.pdf .
else
  echo "\n  === ERROR WHILE COMPILING (SEE ABOVE) ===" >&1
  exit 1
fi