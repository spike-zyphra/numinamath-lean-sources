import Mathlib

theorem number_theory_52385 : IsSquare (∑ n in Finset.Icc 0 2013, Nat.factorial 4026 / (Nat.factorial n * Nat.factorial (2013 - n))^2) := by
  native_decide