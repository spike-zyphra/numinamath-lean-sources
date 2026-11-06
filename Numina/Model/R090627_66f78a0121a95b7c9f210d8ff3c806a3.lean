import Mathlib

theorem inequalities_3122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≤ 1) (h2 : b ≤ 1) (h3 : c ≤ 1) :
    a / (1 + b + c * a) + b / (1 + c + a * b) + c / (1 + a + b * c) ≤
    3 / (a + b + c) := by

  have h4 : a + b + c > 0 := by
    nlinarith

  have h11 : a / (1 + b + c * a) ≤ 1 / (a + b + c) := by
    have h4' : 0 < 1 + b + c * a := by nlinarith
    have h4'' : 0 < a + b + c := by nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - b by linarith),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h12 : b / (1 + c + a * b) ≤ 1 / (a + b + c) := by
    have h4' : 0 < 1 + c + a * b := by nlinarith
    have h4'' : 0 < a + b + c := by nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - b by linarith),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h13 : c / (1 + a + b * c) ≤ 1 / (a + b + c) := by
    have h4' : 0 < 1 + a + b * c := by nlinarith
    have h4'' : 0 < a + b + c := by nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - b by linarith),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h14 : a / (1 + b + c * a) + b / (1 + c + a * b) + c / (1 + a + b * c) ≤ 1 / (a + b + c) + 1 / (a + b + c) + 1 / (a + b + c) := by
    linarith [h11, h12, h13]

  have h15 : 1 / (a + b + c) + 1 / (a + b + c) + 1 / (a + b + c) = 3 / (a + b + c) := by
    field_simp
    <;> ring

  linarith [h14, h15]