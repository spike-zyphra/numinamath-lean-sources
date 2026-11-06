import Mathlib

open Real

theorem Algebra_24661 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a ^ 5 + b ^ 5 + a * b) +
    b * c / (b ^ 5 + c ^ 5 + b * c) +
    c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 := by

  have h1 : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
    have h2 : a ^ 5 + b ^ 5 ≥ a ^ 2 * b ^ 2 * (a + b) := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * b - b * a),
        sq_nonneg (a ^ 2 * b - a * b ^ 2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h3 : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := by
      have hab : 0 < a * b := mul_pos ha hb
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h4 : 1 / (a * b * (a + b) + 1) = c / (a + b + c) := by
      field_simp
      nlinarith [habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    rw [h4] at h3
    exact h3

  have h2 : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by
    have h5 : b ^ 5 + c ^ 5 ≥ b ^ 2 * c ^ 2 * (b + c) := by
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b * c - c * b),
        sq_nonneg (b ^ 2 * c - b * c ^ 2), mul_pos hb hc, mul_pos ha hb, mul_pos ha hc]
    have h6 : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := by
      have hbc : 0 < b * c := mul_pos hb hc
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c),
        mul_pos hb hc, mul_pos ha hb, mul_pos ha hc]
    have h7 : 1 / (b * c * (b + c) + 1) = a / (a + b + c) := by
      field_simp
      nlinarith [habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    rw [h7] at h6
    exact h6

  have h3 : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (a + b + c) := by
    have h8 : c ^ 5 + a ^ 5 ≥ c ^ 2 * a ^ 2 * (c + a) := by
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c * a - a * c),
        sq_nonneg (c ^ 2 * a - c * a ^ 2), mul_pos hc ha, mul_pos ha hb, mul_pos hb hc]
    have h9 : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 / (c * a * (c + a) + 1) := by
      have hca : 0 < c * a := mul_pos hc ha
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (c ^ 2 * a - a ^ 2 * c), sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a),
        mul_pos hc ha, mul_pos ha hb, mul_pos hb hc]
    have h10 : 1 / (c * a * (c + a) + 1) = b / (a + b + c) := by
      field_simp
      nlinarith [habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    rw [h10] at h9
    exact h9

  have h4 : a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a) ≤ c / (a + b + c) + a / (a + b + c) + b / (a + b + c) := by linarith [h1, h2, h3]

  have h5 : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = 1 := by
    field_simp
    <;> nlinarith

  linarith [h4, h5]