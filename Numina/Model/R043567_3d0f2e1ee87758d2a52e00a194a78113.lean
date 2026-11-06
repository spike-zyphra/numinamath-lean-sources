import Mathlib

theorem inequalities_248259 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h2 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    have h : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb]
    linarith
  have h3 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    have h : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc]
    linarith
  have h4 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    have h : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := by
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), mul_pos hc ha]
    linarith
  have h5 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h2]
  have h6 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h3]
  have h7 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h4]
  have h8 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    ring
  have h9 : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
    linarith [h5, h6, h7]
  linarith [h8, h9]