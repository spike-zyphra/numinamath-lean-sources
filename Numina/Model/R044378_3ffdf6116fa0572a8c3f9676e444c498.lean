import Mathlib

open Real

theorem inequalities_597722 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    1 / ((1 + a ^ 2) * (1 + b ^ 2)) +
    1 / ((1 + b ^ 2) * (1 + c ^ 2)) +
    1 / ((1 + c ^ 2) * (1 + a ^ 2)) ≤
    1 / (8 * a * b * c) * (1 / (a + b) +
    1 / (b + c) +
    1 / (c + a)) := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : 1 / ((1 + a ^ 2) * (1 + b ^ 2)) ≤ 1 / (8 * a * b * c * (a + b)) := by
    have h3 : 0 < (1 + a ^ 2) * (1 + b ^ 2) := by
      positivity
    have h4 : 0 < 8 * a * b * c * (a + b) := by
      positivity
    have h5 : (1 + a ^ 2) * (1 + b ^ 2) ≥ 8 * a * b * c * (a + b) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  have h3 : 1 / ((1 + b ^ 2) * (1 + c ^ 2)) ≤ 1 / (8 * a * b * c * (b + c)) := by
    have h3 : 0 < (1 + b ^ 2) * (1 + c ^ 2) := by
      positivity
    have h4 : 0 < 8 * a * b * c * (b + c) := by
      positivity
    have h5 : (1 + b ^ 2) * (1 + c ^ 2) ≥ 8 * a * b * c * (b + c) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  have h4 : 1 / ((1 + c ^ 2) * (1 + a ^ 2)) ≤ 1 / (8 * a * b * c * (c + a)) := by
    have h3 : 0 < (1 + c ^ 2) * (1 + a ^ 2) := by
      positivity
    have h4 : 0 < 8 * a * b * c * (c + a) := by
      positivity
    have h5 : (1 + c ^ 2) * (1 + a ^ 2) ≥ 8 * a * b * c * (c + a) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  have h5 : 1 / (8 * a * b * c * (a + b)) + 1 / (8 * a * b * c * (b + c)) + 1 / (8 * a * b * c * (c + a)) =
      1 / (8 * a * b * c) * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
    field_simp
    all_goals ring

  linarith [h2, h3, h4, h5]