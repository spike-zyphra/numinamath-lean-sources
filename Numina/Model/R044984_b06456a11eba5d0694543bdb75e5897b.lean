import Mathlib

open Real

theorem inequalities_602273 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
    a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 9 / 10 := by
  have h1 : a / (1 + a ^ 2) ≤ (36 * a + 3) / 50 := by
    have h2 : 0 < 1 + a ^ 2 := by
      nlinarith [sq_pos_of_pos ha]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a + 3 / 4), sq_pos_of_pos ha, sq_nonneg (a - 1 / 3), mul_pos ha (show 0 < a by linarith), sq_nonneg (a^2 - 1 / 9)]
  have h2 : b / (1 + b ^ 2) ≤ (36 * b + 3) / 50 := by
    have h3 : 0 < 1 + b ^ 2 := by
      nlinarith [sq_pos_of_pos hb]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1 / 3), sq_nonneg (b + 3 / 4), sq_pos_of_pos hb, sq_nonneg (b - 1 / 3), mul_pos hb (show 0 < b by linarith), sq_nonneg (b^2 - 1 / 9)]
  have h3 : c / (1 + c ^ 2) ≤ (36 * c + 3) / 50 := by
    have h4 : 0 < 1 + c ^ 2 := by
      nlinarith [sq_pos_of_pos hc]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1 / 3), sq_nonneg (c + 3 / 4), sq_pos_of_pos hc, sq_nonneg (c - 1 / 3), mul_pos hc (show 0 < c by linarith), sq_nonneg (c^2 - 1 / 9)]
  have h4 : a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ (36 * a + 3) / 50 + (36 * b + 3) / 50 + (36 * c + 3) / 50 := by
    linarith [h1, h2, h3]
  have h5 : (36 * a + 3) / 50 + (36 * b + 3) / 50 + (36 * c + 3) / 50 = 9 / 10 := by
    linarith [h]
  linarith [h4, h5]