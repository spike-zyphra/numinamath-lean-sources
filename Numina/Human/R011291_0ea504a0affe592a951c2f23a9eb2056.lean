import Mathlib

theorem inequalities_107623 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    3 / 2 ≤ 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) := by
  have h1 : 1 / (1 + a * b) ≥ (3 - a * b) / 4 := by
    have h_pos : 0 < 1 + a * b := by nlinarith [mul_pos ha hb]
    have h3 : (3 - a * b) / 4 ≤ 1 / (1 + a * b) := by
      have h4 : 0 < 1 + a * b := by nlinarith [mul_pos ha hb]
      have h5 : (3 - a * b) * (1 + a * b) ≤ 4 := by
        nlinarith [sq_nonneg (a * b - 1)]
      apply (le_div_iff₀' h4).mpr
      linarith
    linarith
  have h2 : 1 / (1 + b * c) ≥ (3 - b * c) / 4 := by
    have h_pos : 0 < 1 + b * c := by nlinarith [mul_pos hb hc]
    have h3 : (3 - b * c) / 4 ≤ 1 / (1 + b * c) := by
      have h4 : 0 < 1 + b * c := by nlinarith [mul_pos hb hc]
      have h5 : (3 - b * c) * (1 + b * c) ≤ 4 := by
        nlinarith [sq_nonneg (b * c - 1)]
      apply (le_div_iff₀' h4).mpr
      linarith
    linarith
  have h3 : 1 / (1 + c * a) ≥ (3 - c * a) / 4 := by
    have h_pos : 0 < 1 + c * a := by nlinarith [mul_pos hc ha]
    have h3 : (3 - c * a) / 4 ≤ 1 / (1 + c * a) := by
      have h4 : 0 < 1 + c * a := by nlinarith [mul_pos hc ha]
      have h5 : (3 - c * a) * (1 + c * a) ≤ 4 := by
        nlinarith [sq_nonneg (c * a - 1)]
      apply (le_div_iff₀' h4).mpr
      linarith
    linarith
  have h4 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) ≥ (9 - (a * b + b * c + c * a)) / 4 := by
    linarith [h1, h2, h3]
  have h5 : a * b + b * c + c * a ≤ 3 := by
    have h6 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h]
  linarith [h4, h5]
