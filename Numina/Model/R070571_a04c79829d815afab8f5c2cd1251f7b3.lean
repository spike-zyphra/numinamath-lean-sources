import Mathlib

theorem inequalities_69640 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 1 / 9 + 15 * a * b * c := by
  have h1 : c = 1 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg ((1 - a - b) - 1 / 3), mul_pos ha hb, mul_pos hb (show 0 < (1 - a - b) by nlinarith), mul_pos ha (show 0 < (1 - a - b) by nlinarith)]