import Mathlib

/- Find the sum of the reciprocals of all the (positive) divisors of 144.-/
theorem number_theory_611156 : ∑ d in (Nat.divisors 144), (1 : ℚ) / d = (403 / 144 : ℚ) := by
  -- We first find that divisors of 144.
  rw [show Nat.divisors 144 = {1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} by decide]
  -- Then compute their reciprocal sums directly to verify it's equal to 403/144.
  simp
  norm_num