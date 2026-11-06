import Mathlib

theorem inequalities_209859
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 1) :
    27 * (a^3 + b^3 + c^3) ≥ 6 * (a^2 + b^2 + c^2) + 1 ∧
    27 * (a^3 + b^3 + c^3) + 1 ≥ 12 * (a^2 + b^2 + c^2) := by
  have hc1 : c = 1 - a - b := by
    linarith
  constructor
  · -- Prove the first inequality
    rw [hc1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
      sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg ((1 - a - b) - 1 / 3),
      mul_pos ha hb, 
      mul_pos hb (show 0 < 1 - a - b by nlinarith [ha, hb, hc1, h]), 
      mul_pos ha (show 0 < 1 - a - b by nlinarith [ha, hb, hc1, h])]
  · -- Prove the second inequality
    rw [hc1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
      sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg ((1 - a - b) - 1 / 3),
      mul_pos ha hb, 
      mul_pos hb (show 0 < 1 - a - b by nlinarith [ha, hb, hc1, h]), 
      mul_pos ha (show 0 < 1 - a - b by nlinarith [ha, hb, hc1, h])]