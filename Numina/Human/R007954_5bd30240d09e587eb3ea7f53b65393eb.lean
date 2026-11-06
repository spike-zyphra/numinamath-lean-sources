import Mathlib

/- How many digits are in the whole-number representation of $10^{100}-9^{100}$? -/
theorem number_theory_23070 : (Nat.digits 10 (10^100 - 9^100)).length = 100 := by
  simp