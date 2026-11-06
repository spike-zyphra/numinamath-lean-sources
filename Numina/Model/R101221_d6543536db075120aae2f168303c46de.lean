import Mathlib

theorem number_theory_4657 : (101^3-19*101-30).gcd (2^3*3*13*103) = 2^3*3*13*103 := by 
  norm_num [Nat.gcd]