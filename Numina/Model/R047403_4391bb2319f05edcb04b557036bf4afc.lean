import Mathlib

theorem inequalities_598392 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 4) :
    1 / (11 + a ^ 2) + 1 / (11 + b ^ 2) + 1 / (11 + c ^ 2) + 1 / (11 + d ^ 2) ≤ 1 / 3 := by

  have h1 : 1 / (11 + a ^ 2) ≤ (7 - a) / 72 := by
    have h2 : 0 < (11 + a^2 : ℝ) := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1)]

  have h2 : 1 / (11 + b ^ 2) ≤ (7 - b) / 72 := by
    have h3 : 0 < (11 + b^2 : ℝ) := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1)]

  have h3 : 1 / (11 + c ^ 2) ≤ (7 - c) / 72 := by
    have h4 : 0 < (11 + c^2 : ℝ) := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1)]

  have h4 : 1 / (11 + d ^ 2) ≤ (7 - d) / 72 := by
    have h5 : 0 < (11 + d^2 : ℝ) := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (d - 1)]

  have h5 : 1 / (11 + a ^ 2) + 1 / (11 + b ^ 2) + 1 / (11 + c ^ 2) + 1 / (11 + d ^ 2) ≤ (7 - a) / 72 + (7 - b) / 72 + (7 - c) / 72 + (7 - d) / 72 := by
    linarith [h1, h2, h3, h4]

  have h6 : (7 - a) / 72 + (7 - b) / 72 + (7 - c) / 72 + (7 - d) / 72 = 1 / 3 := by
    have h11 : a + b + c + d = 4 := h
    linarith

  linarith [h5, h6]