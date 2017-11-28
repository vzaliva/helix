#!/bin/bash

A=bug1.v
B=bug2.v

while :
do
    rm -f $B
    echo "Stripping"
    ./strip_proofs.py < $A > $B
    diff -u $A $B
    if [ $? -eq 0 ]; then
        echo "All Done!"
        exit 0
    fi
    echo "Compiling"
    coqc -w none $B
    if [ $? -ne 0 ]; then
        echo "Compilation failed"
        exit 1
    fi    
    echo "Saving"
    mv $A "$A.bak"
    mv $B $A
done
