import Mathlib

theorem inequalities_240161 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≤ 3) :
    (a + 1) / (a * (a + 2)) + (b + 1) / (b * (b + 2)) +
    (c + 1) / (c * (c + 2)) ≥ 2 := by

  have h3 : (a + 1) / (a * (a + 2)) ≥ (11 / 9) - (5 / 9) * a := by
    have h8 : 0 < a * (a + 2) := by
      positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 9 / 5), sq_nonneg (a ^ 2), sq_nonneg (a * (a - 1)), mul_pos ha (show 0 < a + 2 by linarith)]

  have h4 : (b + 1) / (b * (b + 2)) ≥ (11 / 9) - (5 / 9) * b := by
    have h8 : 0 < b * (b + 2) := by
      positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 9 / 5), sq_nonneg (b ^ 2), sq_nonneg (b * (b - 1)), mul_pos hb (show 0 < b + 2 by linarith)]

  have h5 : (c + 1) / (c * (c + 2)) ≥ (11 / 9) - (5 / 9) * c := by
    have h8 : 0 < c * (c + 2) := by
      positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 9 / 5), sq_nonneg (c ^ 2), sq_nonneg (c * (c - 1)), mul_pos hc (show 0 < c + 2 by linarith)]

  have h6 : (a + 1) / (a * (a + 2)) + (b + 1) / (b * (b + 2)) + (c + 1) / (c * (c + 2)) ≥ (11 / 9 - 5 / 9 * a) + (11 / 9 - 5 / 9 * b) + (11 / 9 - 5 / 9 * c) := by linarith [h3, h4, h5]

  have h7 : (11 / 9 - 5 / 9 * a) + (11 / 9 - 5 / 9 * b) + (11 / 9 - 5 / 9 * c) = 33 / 9 - (5 / 9) * (a + b + c) := by ring

  have h8 : (33 / 9 - (5 / 9) * (a + b + c)) ≥ (2 : ℝ) := by
    nlinarith

  linarith [h6, h7, h8]