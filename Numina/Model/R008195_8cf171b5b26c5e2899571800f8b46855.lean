import Mathlib

theorem algebra_15391 : (1/3 + 1/4) / (2/5 - 1/6) = (5/2 : ℝ ) ∧ (2).gcd 5 = 1 := by 
  constructor
  · -- Calculate (1/3 + 1/4) / (2/5 - 1/6) and show it equals 5/2
    norm_num
  · -- Show that the greatest common divisor of 2 and 5 is 1
    norm_num [Nat.gcd]