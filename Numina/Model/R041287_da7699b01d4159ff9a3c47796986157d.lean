import Mathlib

theorem inequalities_136520 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a^2 + a * b + b^2 ≤ 3 * (a - Real.sqrt (a * b) + b)^2 := by
  have h1 : 0 ≤ a * b := by nlinarith
  have h2 : Real.sqrt (a * b) ≥ 0 := by positivity
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * Real.sqrt (a * b)), sq_nonneg (Real.sqrt (a * b)), sq_nonneg (a - Real.sqrt (a * b)), sq_nonneg (b - Real.sqrt (a * b)), Real.sqrt_nonneg (a * b), Real.sq_sqrt (show (0 : ℝ) ≤ a * b by nlinarith), mul_nonneg (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg (a * b)), sq_nonneg (a + b - Real.sqrt (a * b)), sq_nonneg (a - b), mul_nonneg ha hb, Real.sqrt_nonneg (a * b)]