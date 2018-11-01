; DSHCompose (DSHBinOp (AZless (AVar 1) (AVar 0)))
;   (DSHHTSUMUnion (APlus (AVar 1) (AVar 0))
;      (DSHCompose (DSHeUnion (NConst 0) CarrierAz)
;         (DSHIReduction 3 (APlus (AVar 1) (AVar 0)) CarrierAz
;            (DSHCompose
;               (DSHCompose (DSHPointwise (AMult (AVar 0) (ANth 3 (VVar 3) (NVar 2))))
;                  (DSHInductor (NVar 0) (AMult (AVar 1) (AVar 0)) CarrierA1))
;               (DSHeT (NConst 0)))))
;      (DSHCompose (DSHeUnion (NConst 1) CarrierAz)
;         (DSHIReduction 2 (AMax (AVar 1) (AVar 0)) CarrierAz
;            (DSHCompose (DSHBinOp (AAbs (AMinus (AVar 1) (AVar 0))))
;               (DSHIUnion 2 (APlus (AVar 1) (AVar 0)) CarrierAz
;                  (DSHCompose (DSHeUnion (NVar 0) CarrierAz)
;                     (DSHeT
;                        (NPlus (NPlus (NConst 1) (NMult (NVar 1) (NConst 1)))
;                           (NMult (NVar 0) (NMult (NConst 2) (NConst 1)))))))))))
;      : DSHOperator (1 + 4) 1

; c2 := func(TInt, "transform", [ X, D ], 
;        decl([ q7, q8, s12, s13, s14, s15, s16, s9, w2 ],
;           chain(
;              assign(s13, V(0.0)),
;              assign(s16, nth(X, V(0))),
;              assign(s15, V(1.0)),
;              loop(i17, [ 0 .. 2 ],
;                 chain(
;                    assign(s14, mul(s15, nth(D, i17))),
;                    assign(s13, add(s13, s14)),
;                    assign(s15, mul(s15, s16))
;                 )
;              ),
;              assign(s9, V(0.0)),
;              loop(i15, [ 0 .. 1 ],
;                 chain(
;                    assign(q7, nth(X, add(i15, V(1)))),
;                    assign(q8, nth(X, add(V(3), i15))),
;                    assign(w2, sub(q7, q8)),
;                    assign(s12, cond(geq(w2, V(0)), w2, neg(w2))),
;                    assign(s9, cond(geq(s9, s12), s9, s12))
;                 )
;              ),
;              creturn(geq(s9, s13))
;           )
;        )
;     ) )


target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@D = external global [3 x double]* align 16

define i1 @dynwin([5 x double]* align 16 %X, [1 x double]* align 16 %Y)
{
    %b = call noalias i8* @malloc(i64 64)
    %y = bitcast i8* %b to [8 x double]*
    
    br label %entry

entry:
    br label %loop
  
loop:
    %i = phi i64 [ 0, %entry ], [ %nextvar, %loop ]

    ; body
    %px = getelementptr [8 x double], [8 x double]* %x, i64 0, i64 %i
    %v = load double, double* %px, align 8
    %u = call double %f (double %v)
    %py = getelementptr [8 x double], [8 x double]* %y, i64 0, i64 %i
    store double %u, double* %py, align 8
    
    ; increment
    %nextvar = add i64 %i, 1
    ; termination test
    %loopcond = icmp ne i64 %i, 7
    br i1 %loopcond, label %loop, label %afterloop

afterloop:
    ret [8 x double]* %y
}
