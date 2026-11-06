import Mathlib

theorem inequalities_603738 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h1 : a ^ 3 + b ^ 3 ≥ a ^ 2 * b + a * b ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have h2 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals linarith [h2]
  have h4 : b ^ 3 + c ^ 3 ≥ b ^ 2 * c + b * c ^ 2 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
  have h5 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h6 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals linarith [h5]
  have h7 : c ^ 3 + a ^ 3 ≥ c ^ 2 * a + c * a ^ 2 := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]
  have h8 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [h7, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h9 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals linarith [h8]
  have h10 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    <;> ring
  linarith [h3, h6, h9, h10]