import Mathlib

theorem inequalities_45939 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a^3 + b^3 + a * b * c) +
    1 / (b^3 + c^3 + a * b * c) +
    1 / (c^3 + a^3 + a * b * c) ≤
    1 / (a * b * c) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : a^3 + b^3 ≥ a * b * (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - b), mul_pos ha hb]

  have h3 : b^3 + c^3 ≥ b * c * (b + c) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b - c), mul_pos hb hc]

  have h4 : c^3 + a^3 ≥ c * a * (c + a) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c - a), mul_pos hc ha]

  have h5 : a^3 + b^3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith

  have h6 : b^3 + c^3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith

  have h7 : c^3 + a^3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith

  have h8 : 1 / (a^3 + b^3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals linarith [h5]

  have h9 : 1 / (b^3 + c^3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals linarith [h6]

  have h10 : 1 / (c^3 + a^3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals linarith [h7]

  have h11 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) =
      1 / (a * b * c) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring

  linarith [h8, h9, h10, h11]