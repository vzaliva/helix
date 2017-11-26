#!/usr/bin/env python

import sys

proof=""
inproof = False

for s in sys.stdin:
    if inproof:
        if s.strip() == "Qed."  or s.strip() == "Admitted.":
            sys.stdout.write("Admitted.\n")
            proof = ""
            inproof = False
        elif s.strip() == "Defined.":
            sys.stdout.write(proof)
            sys.stdout.write(s)
            proof = ""
            inproof = False
        else:
            proof += s
    else:
        if s.strip() == "Proof.":
            inproof = True
            proof += s
        else:
            sys.stdout.write(s)
            
        
