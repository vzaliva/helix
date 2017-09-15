Load(packages.hacms);
Import(packages.hacms);

TraceToFile("trace.log");

d := var("D", TPtr(TReal));
name := "dwmonitor";
opts := HACMSopts.getOpts(rec(globalUnrolling := 2, useCReturn := true, params := [d], includes := ["\""::name::".h\""]));

t := TLess(TEvalPolynomial(2, d), TDistance(TInfinityNorm(2)));

res := CoSynthesize(t, opts);
