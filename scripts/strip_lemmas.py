#!/usr/bin/env python3

import sys
import re

inlemma = False

lemma = re.compile(r"^\s*((Global|Local)\s+)?(Lemma|Theorem|Fact|Remark|Corollary|Proposition)\s+.*")

for s in sys.stdin:
    ss = s.strip()
    if inlemma:
        if ss == "Qed." or ss == "Admitted." or  ss == "Defined.":
            inlemma = False
    else:
        if re.fullmatch(lemma,ss):
            inlemma = True
        else:
            sys.stdout.write(s)
            
        
