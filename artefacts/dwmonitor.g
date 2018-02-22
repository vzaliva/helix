Load(packages.hacms);
Import(packages.hacms);

Value.print := self>>Print("Value(",self.t,", ", self.v, ")");
ExportCode := function(c)
    local vars;
    vars := FoldL(Collect(c, var), (a,b)->When(not b.id in List(a, i->i.id), Concat([b],a), a), []);
    Print("let(", DoForAll(vars, i->Print(i.id, " := var(\"", i.id, "\", ", i.t, "),\n")), c, ")");
end;

TraceToFile("trace.log");

d := var("D", TPtr(TReal));
name := "dwmonitor";
doc := 
    "/*\tDynamic Window Approach Safety Monitor\n"::
    "\n"::
    "\tinputs:\n"::
    "\tD[0] = (A/b+1)*(A/2*eps^2+eps*V)\n"::
    "\tD[1] = V/b + eps*(A/b+1)\n"::
    "\tD[2] = 1/(2*b)\n"::
    "\n"::
    "\tX[0] = vr\n"::
    "\tX[1..2] = pr.x, pr.y\n"::
    "\tx[3..4] = po.x, po.y\n"::
    "\n"::
    "\tcomputes:\n"::
    "\t(A/b+1)*(A/2*eps^2+eps*V) + (V/b + eps*(A/b+1))*vr + (1/(2*b))*vr^2 < || pr - po||_oo\n"::
    "\n"::
    "\treturn:\n"::
    "\t1 => true\n"::
    "\t0 => false\n"::
    "\t-1 => unknown\n"::
    "\n*/\n";

opts := HACMSopts.getOpts(rec(globalUnrolling := 2, useCReturn := true, params := [d], includes := ["\""::name::".h\""]));

t := TLess(TEvalPolynomial(2, d), TDistance(TInfinityNorm(2)));

res := CoSynthesize(t, opts);

PrintTo(name::".c", ExportCProg(res, opts));
PrintTo(name::".g", ExportCode(res));
PrintTo(name::".h", ExportInclude(res, opts));

