import Mathlib

theorem algebra_811 (a b c d : ℝ) (h1 : 0 < a) (h2 : 0 < b) (h3 : 0 < c) (h4 : 0 < d)
    (h5 : 1 / a + 1 / b + 1 / c = 1 / 12) (h6 : 1 / b + 1 / c + 1 / d = 1 / 15)
    (h7 : 1 / a + 1 / d = 1 / 20) :
    1 / a + 1 / b + 1 / c + 1 / d = 1 / 10 := by
  field_simp at h5 h6 h7 ⊢
  nlinarith [mul_pos h1 h2, mul_pos h1 h3, mul_pos h1 h4, mul_pos h2 h3, mul_pos h2 h4, mul_pos h3 h4]