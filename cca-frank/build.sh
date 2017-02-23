#!/bin/sh

set -e
if pdflatex -shell-escape -interaction=nonstopmode -output-directory output frank.tex; then
  cp output/frank.pdf .
else
  echo "\n  === ERROR WHILE COMPILING (SEE ABOVE) ===" >&1
  exit 1
fi