import Mathlib

theorem number_theory_15785 : gcd (83^9 + 1) (83^9 + 83^2 + 1) = 1 := by
  norm_num [gcd]