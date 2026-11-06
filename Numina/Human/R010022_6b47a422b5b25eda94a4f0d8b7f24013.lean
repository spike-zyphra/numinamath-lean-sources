import Mathlib

/- What is the value of $25_{10}+36_{10}$ in base 3?-/
theorem number_theory_12780 : Nat.digits 3 (25 + 36) = [1, 2, 0, 2] := by
  -- convert the sum to base 3, trivial calculation
  simp