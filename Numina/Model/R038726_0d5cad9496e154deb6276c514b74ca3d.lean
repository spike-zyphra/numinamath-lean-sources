import Mathlib

theorem algebra_290528 (α : ℝ) (h : 3 * Real.tan α - Real.sin α + 4 * Real.cos α = 12) :
    Real.tan α = 4 := by
  have htan : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]
  have hc : Real.cos α ≠ 0 := by
    by_contra h0
    have h0' : Real.tan α = 0 := by
      rw [htan]
      simp [h0]
    rw [h0'] at h
    have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    nlinarith [h0, h3]
  have sin_eq : Real.sin α = Real.tan α * Real.cos α := by
    rw [htan]
    field_simp [hc]
    <;> nlinarith [Real.sin_sq_add_cos_sq α]
  rw [sin_eq] at h
  have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have htan_eq : Real.tan α = 4 := by
    have h2 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := h3
    field_simp [hc] at h h2 ⊢
    nlinarith [sq_nonneg (Real.sin α ^ 2 + Real.cos α ^ 2 - 1), sq_nonneg (Real.sin α - 4 / Real.sqrt 17), sq_nonneg (Real.cos α - 1 / Real.sqrt 17), Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α + 4 / Real.sqrt 17), sq_nonneg (Real.cos α + -1 / Real.sqrt 17), sq_nonneg (Real.tan α - 4), sq_pos_of_pos (show 0 < Real.sqrt 17 by norm_num [Real.sqrt_pos]), Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num)]
  exact htan_eq