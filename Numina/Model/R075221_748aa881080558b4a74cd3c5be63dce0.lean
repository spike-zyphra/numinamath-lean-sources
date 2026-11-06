import Mathlib

theorem inequalities_603330 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h1 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h2 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - a), sq_nonneg (c - a),
      sq_nonneg (b + c - a), sq_nonneg (c + a - b), sq_nonneg (a + b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h3 : c ^ 3 + a ^ 3 + a * b * c ≥ a * c * (a + b + c) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (b - a),
      sq_nonneg (c + a - b), sq_nonneg (a + b - c), sq_nonneg (b + c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h4 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  have h5 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  have h6 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  have h8 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    <;> ring_nf <;> field_simp <;> ring

  linarith [h4, h5, h6, h8]