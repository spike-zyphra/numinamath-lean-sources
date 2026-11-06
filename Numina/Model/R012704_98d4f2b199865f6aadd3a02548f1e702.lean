import Mathlib

theorem inequalities_56536 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a + b ≤ c + 1) (h2 : b + c ≤ a + 1) (h3 : c + a ≤ b + 1) :
    a^2 + b^2 + c^2 ≤ 2 * a * b * c + 1 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
          mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), 
          mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h3), 
          mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3)]