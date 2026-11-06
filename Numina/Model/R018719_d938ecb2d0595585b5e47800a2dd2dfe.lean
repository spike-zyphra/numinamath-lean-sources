import Mathlib

theorem inequalities_601669
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    2 ≤ (1 - a^2)^2 + (1 - b^2)^2 + (1 - c^2)^2 := by
  have hc2 : c = 1 - a - b := by
    linarith
  rw [hc2]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), sq_nonneg (a + b - 1), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), sq_nonneg ((1 - a - b) - 1/2), mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), mul_nonneg (show 0 ≤ 1 - a - b by nlinarith) ha]