import Mathlib

theorem algebra_310764 {α β : ℝ} (h : α^2 - 7 * α + 8 = 0) (h' : β^2 - 7 * β + 8 = 0)
    (h'' : α > β) : (2 / α) + 3 * β^2 = (403 - 85 * Real.sqrt 17) / 8 := by
  have h1 : α ≠ 0 := by
    by_contra h1
    rw [h1] at h
    nlinarith
  have h2 : β ≠ 0 := by
    by_contra h2
    rw [h2] at h'
    nlinarith
  have h3 : α^2 - 7 * α + 8 = 0 := h
  have h4 : β^2 - 7 * β + 8 = 0 := h'
  have h5 : (α - β) * (α + β - 7) = 0 := by
    nlinarith
  cases (mul_eq_zero.1 h5) with
  | inl h6 =>
    exfalso
    have h7 : α = β := by linarith
    have h8 : α > β := h''
    nlinarith
  | inr h6 =>
    have h6' : α + β = 7 := by linarith
    have h7 : α * β = 8 := by
      nlinarith [h3, h4, sq_pos_of_pos (show 0 < α - β by linarith), sq_nonneg (α - β)]
    have hα_eq : (α - (7 + Real.sqrt 17) / 2) * (α - (7 - Real.sqrt 17) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num)]
    cases (mul_eq_zero.1 hα_eq) with
    | inl hα1 =>
      have hα : α = (7 + Real.sqrt 17) / 2 := by linarith
      have h12 : β = (7 - Real.sqrt 17) / 2 := by 
        nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_nonneg (Real.sqrt 17)]
      rw [hα, h12]
      field_simp [(show (7 + Real.sqrt 17) / 2 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)])]
      nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_nonneg (Real.sqrt 17), sq_nonneg ((7 - Real.sqrt 17) / 2), sq_nonneg ((7 + Real.sqrt 17) / 2)]
    | inr hα2 =>
      have hα : α = (7 - Real.sqrt 17) / 2 := by linarith
      have h12 : β = (7 + Real.sqrt 17) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_nonneg (Real.sqrt 17)]
      have h13 : α < β := by
        nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), h12, hα]
      linarith