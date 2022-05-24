@rnd64 = float<ieee_64, ne>;

x = rnd64(x_);
y = rnd64(y_);

l = x * x;
r = y * y;

l64 rnd64= x * x;
r64 rnd64= y * y;

eps1 = 1b-38; # error in computing l; see [metasimple.g]
eps2 = 1b-30; # error in computing r; see [metasimple.g]

# [r64] and [l64] are "sufficiently far apart":
# [l64 < r64 - eps1 - eps2] <=> [d64 > 0]
d64 rnd64= r64 - l64 - eps1 - eps2;

# l <? r
{
     x in [0, 200]
  /\ y in [0, 3000]
  /\ d64 >= 1b-1074 # can't make gappa handle "> 0". using the equivalent ">= <smallest_float>"
  ->
  r - l >= 1b-1074
}
