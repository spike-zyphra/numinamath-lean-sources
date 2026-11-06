import Mathlib

theorem number_theory_19366 : (Nat.factorial 20) = 2 * 10 ^ 18 + 432902008176640000 := by
  norm_num [Nat.factorial]