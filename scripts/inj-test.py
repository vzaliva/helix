#!/usr/bin/env python

m =273
n = 82

def l(t1):
    return (t1%n, t1/n)

def r(t2):
    return (t2/m, t2%m)

def lr(t1):
    return t1/n + (t1%n)*m

def rl(t2):
    return t2/m + (t2%m)*n
    
for t in range(0,m*n):
    # left -> right
    lhs = l(t)
    rhs = r(lr(t))
    if lhs != rhs:
        print "> (%s,%s)\t(%s,%s)" % (lhs+rhs)
    # right to left
    rhs = r(t)
    lhs = l(rl(t))
    if lhs != rhs:
        print "< (%s,%s)\t(%s,%s)" % (lhs+rhs)
        
