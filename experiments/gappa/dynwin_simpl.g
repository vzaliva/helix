@rnd64 = float<ieee_64, ne>;

# poly = a2*v*v + a1*v + a0;
# poly64 rnd64= a2*v*v + a1*v + a0;

poly = ((0.0 + (1.0 * a0)) + ((1.0 * v) * a1)) + (((1.0 * v) * v) * a2);
poly64 rnd64= ((0.0 + (1.0 * a0)) + ((1.0 * v) * a1)) + (((1.0 * v) * v) * a2);

cheb = x - y;
cheb64 rnd64= x - y;

{
    a0 in [0, 12.15]
  /\ a1 in [0.01, 20.6]
  /\ a2 in [0.0833333, 0.5]
  /\ v in [0, 20]
  /\ x in [-5000, 5000]
  /\ y in [-5000, 5000]
  ->
    |poly64 - poly| + |cheb64 - cheb| in ?
}

