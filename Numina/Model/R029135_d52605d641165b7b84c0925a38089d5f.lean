import Mathlib


theorem inequalities_115693
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ a ^ 2 / (a + b * c) + b ^ 2 / (b + a * c) + c ^ 2 / (c + a * b) := by

  have h1 : a ^ 2 / (a + b * c) ≥ (2 * a - 1) / 2 := by
    have h2 : 0 < a + b * c := by
      positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b * c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc, sq_nonneg (a * b - 1), sq_nonneg (a * c - 1)]

  have h2 : b ^ 2 / (b + a * c) ≥ (2 * b - 1) / 2 := by
    have h3 : 0 < b + a * c := by
      positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1), sq_nonneg (a * c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc, sq_nonneg (a * b - 1), sq_nonneg (b * c - 1)]

  have h3 : c ^ 2 / (c + a * b) ≥ (2 * c - 1) / 2 := by
    have h4 : 0 < c + a * b := by
      positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1), sq_nonneg (a * b - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc, sq_nonneg (a * c - 1), sq_nonneg (b * c - 1)]

  have h4 : a ^ 2 / (a + b * c) + b ^ 2 / (b + a * c) + c ^ 2 / (c + a * b) ≥ (2 * a - 1) / 2 + (2 * b - 1) / 2 + (2 * c - 1) / 2 := by
    linarith [h1, h2, h3]

  have h5 : (2 * a - 1) / 2 + (2 * b - 1) / 2 + (2 * c - 1) / 2 ≥ 3 / 2 := by
    have h6 : a + b + c ≥ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    linarith

  linarith [h4, h5]