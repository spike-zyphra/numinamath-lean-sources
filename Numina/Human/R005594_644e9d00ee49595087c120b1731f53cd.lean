import Mathlib

/- What is the sum of all of the distinct prime factors of $25^{3}-27^{2}$ ?-/
theorem algebra_10268 : ∑ p in (Nat.primeFactors (25^3 - 27^2)), p = 28 := by
  -- Note that 25³ - 27² = 2⁴ ⬝ 7² ⬝ 19 only has {2, 7, 19} as prime factors.
  rw [show Nat.primeFactors (25^3 - 27^2) = {2, 7, 19} by native_decide]
  simp