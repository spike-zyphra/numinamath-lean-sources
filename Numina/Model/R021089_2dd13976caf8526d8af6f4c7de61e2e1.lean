import Mathlib

theorem inequalities_159644 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 3) :
    a^2 + b^2 + c^2 + a * b * c ≥ 4 := by
  have h1 : c = 3 - a - b := by linarith 
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (3 - a - b)), sq_nonneg (b - (3 - a - b)),
    mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ (3 - a - b : ℝ) by nlinarith),
    mul_nonneg (show 0 ≤ (3 - a - b : ℝ) by nlinarith) ha,
    mul_nonneg (show 0 ≤ (3 - a - b : ℝ) by nlinarith) (show 0 ≤ (3 - a - b : ℝ) by nlinarith)]