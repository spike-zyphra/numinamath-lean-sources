import Mathlib

open Real

theorem inequalities_316552 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b) / 2 ≥ sqrt (a * b) := by
  have h1 : (sqrt (a * b)) ^ 2 = a * b := by
    rw [Real.sq_sqrt]
    positivity
  have h2 : ((a + b) / 2) ^ 2 ≥ a * b := by
    nlinarith [sq_nonneg (a - b), mul_pos ha hb]
  have h5 : ((a + b) / 2) ^ 2 ≥ (sqrt (a * b)) ^ 2 := by
    nlinarith [h2, h1, Real.sqrt_nonneg (a * b)]
  have h6 : (a + b) / 2 ≥ sqrt (a * b) := by
    nlinarith [Real.sqrt_nonneg (a * b), sq_nonneg ((a + b) / 2 - sqrt (a * b)), h5, Real.sq_sqrt (show 0 ≤ a * b by positivity)]
  exact h6