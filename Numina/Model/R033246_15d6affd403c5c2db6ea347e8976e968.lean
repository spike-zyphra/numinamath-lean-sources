import Mathlib

theorem algebra_18522 (x y : ℕ) (hx : x = 5) (hy : y = 2) :
    Real.sqrt (x^3 - 2^y) = 11 := by
  rw [hx, hy]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num