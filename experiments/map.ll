define double @add_one(double %a)
{
  %b = fadd double %a, 1.0
  ret double %b
}

define [8 x double]* @amap(double (double) *%f, [8 x double]* %x)
{
    %y = alloca [8 x double], align 16
    br label %entry

entry:
    br label %loop
  
loop:
    %i = phi i64 [ 0, %entry ], [ %nextvar, %loop ]

    ; body
    %px = getelementptr [8 x double], [8 x double]* %x, i64 0, i64 %i
    %v = load double, double* %px
    %u = call double %f (double %v)
    %py = getelementptr [8 x double], [8 x double]* %y, i64 0, i64 %i
    store double %u, double* %py
    
    ; increment
    %nextvar = add i64 %i, 1
    ; termination test
    %loopcond = icmp ne i64 %i, 7
    br i1 %loopcond, label %loop, label %afterloop

afterloop:
    ret [8 x double]* %y
}
