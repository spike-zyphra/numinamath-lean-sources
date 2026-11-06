import Mathlib

theorem inequalities_601592 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 9 / 10 := by

  have h1 : a / (a ^ 2 + 1) ≤ (36 * a + 3) / 50 := by
    apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a - 3 / 10), sq_nonneg (a * (a - 1 / 3)), sq_nonneg ((a * 3) - 1), mul_pos ha (show (0 : ℝ) < a ^ 2 + 1 by nlinarith)]

  have h2 : b / (b ^ 2 + 1) ≤ (36 * b + 3) / 50 := by
    apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
    nlinarith [sq_nonneg (b - 1 / 3), sq_nonneg (b - 3 / 10), sq_nonneg (b * (b - 1 / 3)), sq_nonneg ((b * 3) - 1), mul_pos hb (show (0 : ℝ) < b ^ 2 + 1 by nlinarith)]

  have h3 : c / (c ^ 2 + 1) ≤ (36 * c + 3) / 50 := by
    apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
    nlinarith [sq_nonneg (c - 1 / 3), sq_nonneg (c - 3 / 10), sq_nonneg (c * (c - 1 / 3)), sq_nonneg ((c * 3) - 1), mul_pos hc (show (0 : ℝ) < c ^ 2 + 1 by nlinarith)]

  have h4 : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ (36 * a + 3) / 50 + (36 * b + 3) / 50 + (36 * c + 3) / 50 := by
    linarith [h1, h2, h3]

  have h5 : (36 * a + 3) / 50 + (36 * b + 3) / 50 + (36 * c + 3) / 50 = (36 * (a + b + c) + 9) / 50 := by
    ring

  rw [h5] at h4
  rw [show a + b + c = 1 by linarith [h] ] at h4
  norm_num at h4 ⊢
  linarith [h4]