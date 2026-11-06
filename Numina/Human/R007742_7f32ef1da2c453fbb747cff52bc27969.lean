import Mathlib

/- What is the length of the diagonal of a square with side length $50\sqrt{2}$ cm? Express your answer in simplest form. -/
theorem algebra_11262 {a : ℝ} (ha : a = 50 * Real.sqrt 2) :
    Real.sqrt (a^2 + a^2) = 100 := by
  rw [ha]
  norm_num
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> linarith