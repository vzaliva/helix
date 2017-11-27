#!/usr/bin/env python3

import sys
import re

STRIP_INSTANCE_PROOFS = False

proof=""
inproof = False
isintance = False

lemma = re.compile(r"^\s*((Global|Local)\s+)?(Lemma|Theorem|Fact|Remark|Corollary|Proposition)\s+.*")
instance = re.compile(r"^\s*((Global|Local)\s+)?(Instance)\s+.*")

for s in sys.stdin:
    ss = s.strip()
    if inproof:
        if ss == "Qed." or ss == "Admitted.":
            sys.stdout.write("Admitted.\n")
            proof = ""
            inproof = False
            isintance = False
        elif ss == "Defined.":
            sys.stdout.write(proof)
            sys.stdout.write(s)
            proof = ""
            inproof = False
            isintance = False
        else:
            proof += s
    else:
        if re.fullmatch(lemma,ss):
            isintance = False
        if re.fullmatch(instance,ss):
            isintance = True
        if ss == "Proof." and (not(isintance) or STRIP_INSTANCE_PROOFS):
            inproof = True
            proof += s
        else:
            sys.stdout.write(s)
            
        
