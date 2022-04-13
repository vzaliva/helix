@rnd32 = float<ieee_32, ne>;
@rnd64 = float<ieee_64, ne>;

a0 = (A/b + 1) * ((A/2)*e*e + e*V);
a1 = V/b + e*(A/b+1);
a2 = 1/(2*b);

a0_64 rnd64= (A/b + 1) * ((A/2)*e*e + e*V);
a1_64 rnd64= V/b + e*(A/b+1);
a2_64 rnd64= 1/(2*b);

a0_32_of_64 = rnd32(a0_64);
a1_32_of_64 = rnd32(a1_64);
a2_32_of_64 = rnd32(a2_64);

a0_32_of_r = rnd32(a0);
a1_32_of_r = rnd32(a1);
a2_32_of_r = rnd32(a2);

{
     V in [0,20]
  /\ b in [1,6]
  /\ A in [0,5]
  /\ e in [0.01,0.1]
  ->
     |a0_32_of_64 - a0_32_of_r| in ?
  /\ |a1_32_of_64 - a1_32_of_r| in ?
  /\ |a2_32_of_64 - a2_32_of_r| in ?

  /\ a0 in ?
  /\ a1 in ?
  /\ a2 in ?
}
