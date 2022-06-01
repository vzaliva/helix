@rnd64 = float<ieee_64, ne>;

# input values are binary32
## A = rnd32(A_);
## b = rnd32(b_);
## e = rnd32(e_);
## V = rnd32(V_);
## v_r = rnd32(v_r_);

## POLYNOMIAL
# precise
a0 = (A/b + 1) * ((A/2)*e*e + e*V);
a1 = V/b + e*(A/b+1);
a2 = 1/(2*b);
p = a2*v_r*v_r + a1*v_r + a0;

# 64-bit
a0_64 rnd64= (A/b + 1) * ((A/2)*e*e + e*V);
a1_64 rnd64= V/b + e*(A/b+1);
a2_64 rnd64= 1/(2*b);
p64 rnd64= a2_64*v_r*v_r + a1_64*v_r + a0_64;


## CHEBYSHEV
# precise
dx = |rx - ox|;
dy = |ry - oy|;
# MAX function workaround
c = (dx + dy + |dx - dy|) / 2; # = max(dx, dy);

# 64-bit
dx64 rnd64= |rx - ox|;
dy64 rnd64= |ry - oy|;
# MAX function workaround. Note infinite precision.
c64 = (dx64 + dy64 + |dx64 - dy64|) / 2; # = max(dx64, dy64)

## EPSILONS
ep = 5665758678918103b-94; # absolute error between {p, p64}

{
     V in [0,20]
  /\ b in [1,6]
  /\ A in [0,5]
  /\ e in [0.01,0.1]

  /\ v_r in [1b-149, 20]

  /\ rx in [-5000, 5000]
  /\ ry in [-5000, 5000]
  /\ ox in [-5000, 5000]
  /\ oy in [-5000, 5000]

  ->

     |p64 - p| in ?
  /\ |c64 - c| in ? # this doesn't work for some reason
}
