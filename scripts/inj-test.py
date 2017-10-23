#!/usr/bin/env python

m = 12
n = 12

def f1(x):
    return (x/n)+(x%n)*m

for i in range(0,m*n):
    print "%s-%s" % (i,f1(i))


        
