import Mathlib

theorem inequalities_8841
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (h : a + b + c = 3) :
    (3 * a - b * c) * (3 * b - a * c) * (3 * c - a * b) ≤ 8 := by

  have h2 : c = 3 - a - b := by linarith
  rw [h2] at *
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1),
    sq_nonneg (a * b - b * (3 - a - b)), sq_nonneg (b * (3 - a - b) - (3 - a - b) * a), 
    sq_nonneg ((3 - a - b) * a - a * b),
    mul_nonneg (show 0 ≤ (a : ℝ) by linarith) (show 0 ≤ (b : ℝ) by linarith), 
    mul_nonneg (show 0 ≤ (a : ℝ) by linarith) (show 0 ≤ (3 - a - b : ℝ) by nlinarith), 
    mul_nonneg (show 0 ≤ (b : ℝ) by linarith) (show 0 ≤ (3 - a - b : ℝ) by nlinarith)
  ]