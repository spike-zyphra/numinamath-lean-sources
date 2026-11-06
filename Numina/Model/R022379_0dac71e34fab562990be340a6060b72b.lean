import Mathlib

theorem algebra_297368 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a - 1 / b - 1 / (a + b) = 0) :
    (b / a) ^ 3 + (a / b) ^ 3 = 2 * Real.sqrt 5 := by
  have h1 : a * b > 0 := mul_pos ha hb
  have h2 : 0 < a + b := by linarith
  have h3 : b ^ 2 - a * b - a ^ 2 = 0 := by
    have hne1 : a ≠ 0 := ne_of_gt ha
    have hne2 : b ≠ 0 := ne_of_gt hb
    have hne3 : a + b ≠ 0 := by linarith
    field_simp [hne1, hne2, hne3] at h ⊢
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
  have h4 : (b / a) ^ 2 = (b / a) + 1 := by
    have h5 : b ^ 2 = a * b + a ^ 2 := by linarith [h3]
    have h6 : a ≠ 0 := ne_of_gt ha
    field_simp [h6] at *
    nlinarith [h5]
  have h8 : b / a > 0 := by
    apply div_pos
    linarith
    linarith
  have h10 : b / a = (1 + Real.sqrt 5) / 2 := by
    have h11 : ((b / a) - (1 + Real.sqrt 5) / 2) * ((b / a) - (1 - Real.sqrt 5) / 2) = 0 := by
      have h4' : (b / a) ^ 2 = (b / a) + 1 := h4
      nlinarith [h4', Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- Case where $b/a - (1 + \sqrt{5})/2 = 0$
      linarith
    · -- Case where $b/a - (1 - \sqrt{5})/2 = 0$
      have h14 : (b / a) = (1 - Real.sqrt 5) / 2 := by linarith
      have h15 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)
      have h16 : (1 - Real.sqrt 5) / 2 < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
      linarith [h14, h16, h8]
  have h11 : a / b = (Real.sqrt 5 - 1) / 2 := by
    have h12 : a / b = 1 / (b / a) := by
      field_simp
    rw [h12, h10]
    field_simp [(show 1 + Real.sqrt 5 ≠ 0 by positivity)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
  rw [show b / a = (1 + Real.sqrt 5) / 2 by linarith [h10]]
  rw [show a / b = (Real.sqrt 5 - 1) / 2 by linarith [h11]]
  ring_nf
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 ^ 2 - 5)]