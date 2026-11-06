import Mathlib
/- Let a, b, c > 0, and ab + bc + ca = 1. Prove: ∑1/(1+a^2)(1+b^2) ≤ 1/8abc ∑ 1/(a+n)-/
theorem inequalities_597722 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    1 / ((1 + a ^ 2) * (1 + b ^ 2)) +
    1 / ((1 + b ^ 2) * (1 + c ^ 2)) +
    1 / ((1 + c ^ 2) * (1 + a ^ 2)) ≤
    1 / (8 * a * b * c) * (1 / (a + b) +
    1 / (b + c) +
    1 / (c + a)) := by

  have h1 : 1 / ((1 + a ^ 2) * (1 + b ^ 2)) ≤ 1 / (8 * a * b * c) * (1 / (a + b)) := by
    have h2 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
    have h3 : (1 + a^2) * (1 + b^2) ≥ 8 * a * b * c * (a + b) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1 / 3), sq_nonneg (a + b - c), h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h4 : 0 < 8 * a * b * c * (a + b) := by
      apply mul_pos
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h5 : 1 / ((1 + a ^ 2) * (1 + b ^ 2)) ≤ 1 / (8 * a * b * c * (a + b)) := by
      apply one_div_le_one_div_of_le
      nlinarith
      nlinarith
    have h6 : 1 / (8 * a * b * c * (a + b)) = 1 / (8 * a * b * c) * (1 / (a + b)) := by
      field_simp
      <;> ring
    linarith

  have h2 : 1 / ((1 + b ^ 2) * (1 + c ^ 2)) ≤ 1 / (8 * a * b * c) * (1 / (b + c)) := by
    have h2 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
    have h3 : (1 + b^2) * (1 + c^2) ≥ 8 * a * b * c * (b + c) := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b * c - 1 / 3), sq_nonneg (b + c - a), h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h4 : 0 < 8 * a * b * c * (b + c) := by
      apply mul_pos
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h5 : 1 / ((1 + b ^ 2) * (1 + c ^ 2)) ≤ 1 / (8 * a * b * c * (b + c)) := by
      apply one_div_le_one_div_of_le
      nlinarith
      nlinarith
    have h6 : 1 / (8 * a * b * c * (b + c)) = 1 / (8 * a * b * c) * (1 / (b + c)) := by
      field_simp
    linarith

  have h3 : 1 / ((1 + c ^ 2) * (1 + a ^ 2)) ≤ 1 / (8 * a * b * c) * (1 / (c + a)) := by
    have h2 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
    have h3 : (1 + c^2) * (1 + a^2) ≥ 8 * a * b * c * (c + a) := by
      nlinarith [sq_nonneg (c - a), sq_nonneg (c * a - 1 / 3), sq_nonneg (c + a - b), h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h4 : 0 < 8 * a * b * c * (c + a) := by
      apply mul_pos
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h5 : 1 / ((1 + c ^ 2) * (1 + a ^ 2)) ≤ 1 / (8 * a * b * c * (c + a)) := by
      apply one_div_le_one_div_of_le
      nlinarith
      nlinarith
    have h6 : 1 / (8 * a * b * c * (c + a)) = 1 / (8 * a * b * c) * (1 / (c + a)) := by
      field_simp
    linarith

  linarith [h1, h2, h3]