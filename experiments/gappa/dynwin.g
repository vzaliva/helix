@rnd32 = float<ieee_32, ne>;
@rnd64 = float<ieee_64, ne>;

p = a2*v_r*v_r + a1*v_r + a0;

p64 rnd64= a2*v_r*v_r + a1*v_r + a0;
p32 rnd32= a2*v_r*v_r + a1*v_r + a0;

p32_of_r = rnd32(p);
p32_of_64 = rnd32(p64);

{
     a0 in [0, 12.15]
  /\ a1 in [0.01, 20.6]
  /\ a2 in [0.0833333, 0.5]
  /\ v_r in [0, 20]
  ->
  /\ |p32_of_64 - p| in ?
  /\ |p32_of_r - p| in ?
  /\ |p32_of_r - p32_of_64| in ?
  /\ |p64 - p| in ?
  /\ |p32 - p| in ?
}
