target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind
declare i8* @malloc(i64)

define double @add_one(double %a)
{
  %b = fadd double %a, 1.0
  ret double %b
}

define [8 x double]* @amap(double (double) *%f, [8 x double]* align 16 %x)
{
init:
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
    %loopcond = icmp eq i64 %nextvar, 8
    br i1 %loopcond, label %afterloop, label %loop

afterloop:
    ret [8 x double]* %y
}
