import Mathlib

theorem inequalities_267644
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hsum : a + b + c = 1) :
    (1 + a) * (1 + b) * (1 + c) ≥ 8 * (1 - a) * (1 - b) * (1 - c) := by
  have hc1 : c = 1 - a - b := by linarith
  rw [hc1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), sq_nonneg (a + b - (1 - a - b)), mul_pos ha hb, mul_pos ha (show (0 : ℝ) < 1 - a - b from by nlinarith), mul_pos hb (show (0 : ℝ) < 1 - a - b from by nlinarith), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - (1 - a - b)))]