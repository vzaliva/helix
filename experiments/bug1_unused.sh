#!/bin/sh

rm -f bug1.glob bug1.vo 
coqc -w none bug1.v 

rm -f depgraph.vcmd graph.dpd unused.txt

echo "Require dpdgraph.dpdgraph." > depgraph.vcmd
echo "Require bug1." >> depgraph.vcmd
echo "Print FileDependGraph bug1." >> depgraph.vcmd

coqtop  < depgraph.vcmd

dpdusage -with-path graph.dpd | grep -v -i proper | sort > unused.txt
