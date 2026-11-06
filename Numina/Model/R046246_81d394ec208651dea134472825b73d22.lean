import Mathlib

theorem number_theory_143705 :
    Nat.gcd 72 168 = 24 ∧
    Nat.lcm 72 168 = 504 := by
  constructor
  · -- Show that the GCD of 72 and 168 is 24.
    norm_num [Nat.gcd]
  · -- Show that the LCM of 72 and 168 is 504.
    norm_num [Nat.lcm]