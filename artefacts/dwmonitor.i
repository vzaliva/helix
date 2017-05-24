let(i3 := var("i3", TInt),
i5 := var("i5", TInt),
w1 := var("w1", T_Real(64)),
s8 := var("s8", T_Real(64)),
s7 := var("s7", T_Real(64)),
s6 := var("s6", TReal),
s5 := var("s5", T_Real(64)),
s4 := var("s4", TReal),
s1 := var("s1", T_Real(64)),
q4 := var("q4", T_Real(64)),
q3 := var("q3", T_Real(64)),
D := var("D", TPtr(T_Real(64)).aligned([ 16, 0 ])),
X := var("X", TPtr(T_Real(64)).aligned([ 16, 0 ])),
func(TInt, "transform", [ X, D ], 
   decl([ q3, q4, s1, s4, s5, s6, s7, s8, w1 ],
      chain(
         assign(s5, V(0.0)),
         assign(s8, nth(X, V(0))),
         assign(s7, V(1.0)),
         loop(i5, [ 0 .. 2 ],
            chain(
               assign(s6, mul(s7, nth(D, i5))),
               assign(s5, add(s5, s6)),
               assign(s7, mul(s7, s8))
            )
         ),
         assign(s1, V(0.0)),
         loop(i3, [ 0 .. 1 ],
            chain(
               assign(q3, nth(X, add(i3, V(1)))),
               assign(q4, nth(X, add(V(3), i3))),
               assign(w1, sub(q3, q4)),
               assign(s4, cond(geq(w1, V(0)), w1, neg(w1))),
               assign(s1, cond(geq(s1, s4), s1, s4))
            )
         ),
         creturn(geq(s1, s5))
      )
   )
))