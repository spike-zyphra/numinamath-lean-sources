import Mathlib

theorem inequalities_5179 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a^2 + a + 1) * (b^2 + b + 1) * (c^2 + c + 1) ≥ 9 * (a * b + b * c + c * a) := by
  have h1 : c = 3 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a * b - b * (3 - a - b)), sq_nonneg (b * (3 - a - b) - a * (3 - a - b)), sq_nonneg (a * (3 - a - b) - a * b),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1),
    sq_nonneg (a * b + b * (3 - a - b) + a * (3 - a - b) - 3),
    sq_nonneg (a - b), sq_nonneg (a - (3 - a - b)), sq_nonneg (b - (3 - a - b)),
    mul_pos ha hb, mul_pos hb (show 0 < (3 - a - b : ℝ) by nlinarith [h, ha, hb, hc]), mul_pos ha (show 0 < (3 - a - b : ℝ) by nlinarith [h, ha, hb, hc])
          ]