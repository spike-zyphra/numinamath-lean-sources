import Mathlib

theorem algebra_311477 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a - 1 / b - 1 / (a + b) = 0) :
    (b / a)^3 + (a / b)^3 = 2 * Real.sqrt 5 := by

  have h1 : a + b > 0 := by
    linarith

  have eq1 : b * (a + b) = a * (a + 2 * b) := by
    have h2 : a ≠ 0 := by linarith
    have h3 : b ≠ 0 := by linarith
    have h4 : a + b ≠ 0 := by linarith
    field_simp [h2, h3, h4] at h ⊢
    nlinarith [h, mul_pos ha hb, mul_pos ha (show 0 < a + b by linarith), mul_pos hb (show 0 < a + b by linarith)]

  have eq2 : a ^ 2 + a * b - b ^ 2 = 0 := by
    nlinarith

  have h3 : (a / b) ^ 2 + (a / b) - 1 = 0 := by
    have hb2 : b ≠ 0 := by linarith
    have eq4 : (a / b) ^ 2 + (a / b) - 1 = 0 := by
      have eq5 : a ^ 2 + a * b - b ^ 2 = 0 := eq2
      have eq6 : b ^ 2 > 0 := by
        nlinarith
      have eq7 : (a / b) ^ 2 + (a / b) - 1 = (a ^ 2 + a * b - b ^ 2) / b ^ 2 := by
        field_simp [hb2]
        <;> ring
      rw [eq7]
      rw [eq2]
      norm_num
    exact_mod_cast eq4

  have h4 : a / b = (Real.sqrt 5 - 1) / 2 := by
    have h3' : (a / b) ^ 2 + (a / b) - 1 = 0 := h3
    have h5 : (a / b) > 0 := by
      apply div_pos
      linarith
      linarith
    have h5' : (a / b) = (Real.sqrt 5 - 1) / 2 := by
      have h6 : (a / b) ^ 2 + (a / b) - 1 = 0 := h3'
      have h7 : ((a / b) - (Real.sqrt 5 - 1) / 2) * ((a / b) - (-1 - Real.sqrt 5) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case where (a/b) - (sqrt(5) -1)/2 =0
        linarith
      · -- Case where (a/b) - (-1 - sqrt(5))/2 =0
        have h10 : (a / b) < 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        linarith
    linarith

  have h5 : b / a = (Real.sqrt 5 + 1) / 2 := by
    have h4' : a / b = (Real.sqrt 5 - 1) / 2 := h4
    have ha2 : a ≠ 0 := by linarith
    have hb2 : b ≠ 0 := by linarith
    have eq6 : b / a = 1 / (a / b) := by
      field_simp [ha2, hb2]
    rw [eq6, h4']
    have h7 : 1 / ((Real.sqrt 5 - 1) / 2) = (Real.sqrt 5 + 1) / 2 := by
      field_simp [(show (Real.sqrt 5 - 1 : ℝ) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      )]
      <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    exact_mod_cast h7

  rw [h5, h4]
  have h6 : ((Real.sqrt 5 + 1) / 2 : ℝ) ^ 3 + ((Real.sqrt 5 - 1) / 2 : ℝ) ^ 3 = 2 * Real.sqrt 5 := by
    have h7 : ((Real.sqrt 5 + 1) / 2 : ℝ) ^ 3 = Real.sqrt 5 + 2 := by
      nlinarith [sq_nonneg (Real.sqrt 5 ^ 2 - 5), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2)]
    have h8 : ((Real.sqrt 5 - 1) / 2 : ℝ) ^ 3 = Real.sqrt 5 - 2 := by
      nlinarith [sq_nonneg (Real.sqrt 5 ^ 2 - 5), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2)]
    linarith [h7, h8]
  linarith