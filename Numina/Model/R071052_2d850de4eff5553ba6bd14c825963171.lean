import Mathlib

theorem algebra_41837 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 = b^2 + b * c) (h2 : b^2 = c^2 + a * c) :
    1 / c = 1 / a + 1 / b := by
  have h3 : 0 < a * b := mul_pos ha hb
  have h4 : 0 < a * c := mul_pos ha hc
  have h5 : 0 < b * c := mul_pos hb hc
  have h6 : 0 < a * b * c := mul_pos h3 hc
  have h7 : a * b = c * (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h8 : 1 / c = 1 / a + 1 / b := by
    field_simp
    nlinarith [h7, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  exact h8