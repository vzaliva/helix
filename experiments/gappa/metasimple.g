@rnd64 = float<ieee_64, ne>;

x = rnd64(x_);
y = rnd64(y_);

l = x * x;
r = y * y;

l64 rnd64= x * x;
r64 rnd64= y * y;

{
     x in [0, 200]
  /\ y in [0, 3000]
  ->
     |r64 - r| in ? # eps1
  /\ |l64 - l| in ? # eps2
}
