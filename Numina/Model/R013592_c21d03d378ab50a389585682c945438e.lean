import Mathlib

theorem inequalities_598539 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by

  have h1 : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

  have h2 : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]

  have h3 : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]

  have h4 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h5 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h6 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h7 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h8 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h9 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h6, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h10 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) +
    1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    <;> ring

  linarith [h7, h8, h9, h10, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]