import Mathlib

theorem algebra_285405 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) (h4 : 7 / a = 7 / c + 46 / (a + b))
    (h5 : 7 / b = 7 / a + 46 / (a + b)) :
    7 / a = 371 / 60 := by
  have h6 : a * b * c ≠ 0 := by
    positivity
  field_simp [show a ≠ 0 by positivity, show b ≠ 0 by positivity, show c ≠ 0 by positivity, show a + b ≠ 0 by nlinarith [show 0 < a by linarith [ha], show 0 < b by linarith [hb]]] at h4 h5 ⊢
  <;> nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne h1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h3), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]