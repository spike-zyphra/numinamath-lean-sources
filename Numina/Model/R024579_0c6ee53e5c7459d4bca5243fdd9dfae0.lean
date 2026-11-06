import Mathlib

theorem algebra_155976 {α : ℝ} (h : (1 - Real.tan α) / (1 + Real.tan α) = 3 - 2 * Real.sqrt 2) :
    Real.sin (2 * α) = 2 * Real.sqrt 2 / 3 := by
  have h1 : 1 + Real.tan α ≠ 0 := by
    by_contra h2
    have h3 : Real.tan α = -1 := by linarith
    rw [h3] at h
    field_simp [(show (1 + (-1) : ℝ) = (0 : ℝ) by norm_num)] at h
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have eq1 : 1 - Real.tan α = (3 - 2 * Real.sqrt 2) * (1 + Real.tan α) := by
    have h2 : 1 + Real.tan α ≠ 0 := h1
    field_simp [h2] at h ⊢
    nlinarith
  have htan : Real.tan α = Real.sqrt 2 / 2 := by
    have h2 : (1 - Real.tan α : ℝ) = (3 - 2 * Real.sqrt 2) * (1 + Real.tan α) := eq1
    ring_nf at h2 ⊢
    have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.tan α - Real.sqrt 2 / 2)]
  have h5 : Real.sin (2 * α) = 2 * Real.tan α / (1 + Real.tan α ^ 2) := by
    rw [Real.sin_two_mul]
    have htan1 : Real.tan α = Real.sin α / Real.cos α := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan1]
    have h1sin : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    have h1cos : Real.cos α ≠ 0 := by
      by_contra h2
      have htan0 : Real.tan α = 0 := by
        rw [Real.tan_eq_sin_div_cos]
        rw [h2]
        norm_num
      rw [htan0] at htan
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    field_simp [h1sin, h1cos]
    <;> ring
  rw [h5, htan]
  have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  field_simp [h6, pow_two]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]