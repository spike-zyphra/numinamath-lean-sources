import Mathlib

open Real

theorem inequalities_120644 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ sqrt (a * b) := by
  have h1 : 0 ≤ a * b := mul_nonneg ha hb
  have h2 : sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
  have h3 : ((a + b) / 2) ^ 2 ≥ (sqrt (a * b)) ^ 2 := by
    have h4 : (sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (show 0 ≤ a * b by linarith)
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * sqrt (a * b)), h4, Real.sqrt_nonneg (a * b)]
  have h5 : (a + b) / 2 ≥ 0 := by linarith
  nlinarith [h3, Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by linarith), h5]