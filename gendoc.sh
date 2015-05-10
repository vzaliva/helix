#!/bin/sh

rm -f HCOL.pdf
coqdoc --utf8 --pdf --no-index -g -l -s -t "HCOL Coq Formalization" HCOL.v HCOLBreakdown.v -o HCOL.pdf
open HCOL.pdf


