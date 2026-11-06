import Mathlib

theorem algebra_10746 : Nat.lcm (Nat.lcm 6 8) 10 = 120 := by
  norm_num [Nat.lcm]