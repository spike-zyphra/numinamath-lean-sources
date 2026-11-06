import Mathlib

theorem inequalities_599015 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a^3 + b^3 + a * b * c) +
    1 / (b^3 + c^3 + a * b * c) +
    1 / (c^3 + a^3 + a * b * c) ≤
    1 / (a * b * c) := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : a^3 + b^3 ≥ a^2 * b + a * b^2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a), sq_nonneg (b), mul_pos ha hb]

  have h3 : b^3 + c^3 ≥ b^2 * c + b * c^2 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b), sq_nonneg (c), mul_pos hb hc]

  have h4 : c^3 + a^3 ≥ c^2 * a + c * a^2 := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c), sq_nonneg (a), mul_pos hc ha]

  have h5 : a^3 + b^3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h6 : b^3 + c^3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h7 : c^3 + a^3 + a * b * c ≥ a * c * (a + b + c) := by
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h8 : 1 / (a^3 + b^3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h5]

  have h9 : 1 / (b^3 + c^3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h6]

  have h10 : 1 / (c^3 + a^3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h7]

  have h11 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) = 1 / (a * b * c) := by 
    field_simp
    ring

  have h12 : 1 / (a^3 + b^3 + a * b * c) + 1 / (b^3 + c^3 + a * b * c) + 1 / (c^3 + a^3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) := by
    linarith [h8, h9, h10]

  linarith [h12, h11]