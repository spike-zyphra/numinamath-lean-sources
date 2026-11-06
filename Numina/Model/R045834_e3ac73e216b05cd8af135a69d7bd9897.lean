import Mathlib

theorem inequalities_312088 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = a * b * c) :
    1 ≤ (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) +
        (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) +
        (c ^ 4 + a ^ 4) / (a * c * (c ^ 3 + a ^ 3)) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) ≥ (a + b) / (2 * a * b) := by
    have h4 : (a ^ 4 + b ^ 4) ≥ (a + b) * (a ^ 3 + b ^ 3) / 2 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - a * b)]
    have h5 : (a * b * (a ^ 3 + b ^ 3)) > 0 := by positivity
    have h4' : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) ≥ (a + b) / (2 * a * b) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - a * b)]
    linarith

  have h3 : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) ≥ (b + c) / (2 * b * c) := by
    have h4 : (b ^ 4 + c ^ 4) ≥ (b + c) * (b ^ 3 + c ^ 3) / 2 := by
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc, sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - b * c)]
    have h5 : (b * c * (b ^ 3 + c ^ 3)) > 0 := by positivity
    have h4' : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) ≥ (b + c) / (2 * b * c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc, sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - b * c)]
    linarith

  have h4 : (c ^ 4 + a ^ 4) / (a * c * (c ^ 3 + a ^ 3)) ≥ (c + a) / (2 * a * c) := by
    have h5 : (c ^ 4 + a ^ 4) ≥ (c + a) * (c ^ 3 + a ^ 3) / 2 := by
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c + a), mul_pos ha hc, sq_nonneg (c ^ 2 - a * c), sq_nonneg (a ^ 2 - a * c)]
    have h6 : (a * c * (c ^ 3 + a ^ 3)) > 0 := by positivity
    have h5' : (c ^ 4 + a ^ 4) / (a * c * (c ^ 3 + a ^ 3)) ≥ (c + a) / (2 * a * c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c + a), mul_pos ha hc, sq_nonneg (c ^ 2 - a * c), sq_nonneg (a ^ 2 - a * c)]
    linarith

  have h5 : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) + (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) + (c ^ 4 + a ^ 4) / (a * c * (c ^ 3 + a ^ 3)) ≥ (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * a * c) := by linarith [h2, h3, h4]

  have h6 : (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * a * c) = 1 := by
    field_simp at h ⊢
    nlinarith

  linarith [h5, h6]