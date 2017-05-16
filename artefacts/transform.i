func(TInt, "transform", [ X, D ],
     decl([ q7, q8, s12, s13, s14, s15, s16, s9, w2 ],
          chain(
              assign(s13, V(0.0)),
              assign(s16, nth(X, V(0))),
              assign(s15, V(1.0)),
              loop(i17, [ 0 .. 2 ],
                   chain(
                       assign(s14, mul(s15, nth(D, i17))),
                       assign(s13, add(s13, s14)),
                       assign(s15, mul(s15, s16))
                   )
              ),
              assign(s9, V(0.0)),
              loop(i15, [ 0 .. 1 ],
                   chain(
                       assign(q7, nth(X, add(i15, V(1)))),
                       assign(q8, nth(X, add(V(3), i15))),
                       assign(w2, sub(q7, q8)),
                       assign(s12, cond(geq(w2, V(0)), w2, neg(w2))),
                       assign(s9, cond(geq(s9, s12), s9, s12))
                   )
              ),
              creturn(geq(s9, s13))
          )
     )
)
