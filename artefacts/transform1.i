func(TInt, "transform", [ X, D ],
     decl([ T10 ],
          chain(
              chain(
                  decl([ T11 ],
                       chain(
                           chain(
                               assign(nth(T11, V(0)), V(0.0)),
                               loop(i17, [ 0 .. 2 ],
                                    decl([ T12 ],
                                         chain(
                                             decl([ T13, T14 ],
                                                  chain(
                                                      assign(nth(T14, V(0)), nth(X, V(0))),
                                                      assign(nth(T13, V(0)), cond(eq(i17, V(0)), V(1.0), mul(nth(T13, V(0)), nth(T14, V(0))))),
                                                      assign(nth(T12, V(0)), mul(nth(T13, V(0)), nth(D, i17)))
                                                  )
                                             ),
                                             assign(nth(T11, V(0)), add(nth(T11, V(0)), nth(T12, V(0))))
                                         )
                                    )
                               )
                           ),
                           assign(nth(T10, V(0)), nth(T11, V(0)))
                       )
                  ),
                  decl([ T15 ],
                       chain(
                           chain(
                               assign(nth(T15, V(0)), V(0.0)),
                               loop(i15, [ 0 .. 1 ],
                                    decl([ T16 ],
                                         chain(
                                             decl([ T17 ],
                                                  chain(
                                                      loop(i18, [ 0 .. 1 ],
                                                           decl([ T18 ],
                                                                chain(
                                                                    assign(nth(T18, V(0)), nth(X, add(add(i15, V(1)), mul(V(2), i18)))),
                                                                    assign(nth(T17, i18), nth(T18, V(0)))
                                                                )
                                                           )
                                                      ),
                                                      assign(nth(T16, V(0)), abs(sub(nth(T17, V(0)), nth(T17, V(1)))))
                                                  )
                                             ),
                                             assign(nth(T15, V(0)), max(nth(T16, V(0)), nth(T15, V(0))))
                                         )
                                    )
                               )
                           ),
                           assign(nth(T10, V(1)), nth(T15, V(0)))
                       )
                  )
              ),
              assign(nth(Y, V(0)), geq(nth(T10, V(1)), nth(T10, V(0))))
          )
     )
)
