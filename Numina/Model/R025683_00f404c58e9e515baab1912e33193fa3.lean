import Mathlib

theorem inequalities_599999 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h1 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    have h2 : a ^ 3 + b ^ 3 - (a^2 * b + a * b^2) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    nlinarith
  have h2 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    have h3 : b ^ 3 + c ^ 3 - (b^2 * c + b * c^2) ≥ 0 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    nlinarith
  have h4 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    have h5 : c ^ 3 + a ^ 3 - (c^2 * a + c * a^2) ≥ 0 := by
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    nlinarith
  have h6 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    exact h1
  have h7 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    exact h2
  have h8 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    exact h4
  have h9 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    <;> nlinarith
    all_goals field_simp
    all_goals positivity
  have h10 : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    have h11 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := h6
    have h12 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := h7
    have h13 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := h8
    have h14 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := h9
    linarith [h14, h11, h12, h13]
  exact h10