import Mathlib

open Real Set
open scoped Real

theorem calculus_22094 {α β : ℝ} (h₀ : cos (α + β) + sin (α - β) = 0) (h₁ : tan β = 1 / 2000) :
    tan α = -1 := by
  have h2 : cos (α + β) = cos α * cos β - sin α * sin β := by
    rw [cos_add]
  have h3 : sin (α - β) = sin α * cos β - cos α * sin β := by
    rw [sin_sub]
  rw [h2, h3] at h₀
  have h4 : (cos β - sin β) * (cos α + sin α) = 0 := by 
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- case $\cos \beta - \sin \beta = 0$
    have h7 : cos β = sin β := by linarith
    have h8 : tan β = 1 := by
      rw [tan_eq_sin_div_cos]
      have h9 : cos β ≠ 0 := by
        by_contra h11
        have h12 : sin β = 0 := by
          linarith [h7, h11]
        have h13 : sin β ^ 2 + cos β ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq β
        rw [h12, h11] at h13
        nlinarith
      field_simp [h9]
      <;> nlinarith [h7]
    linarith
  · -- case $\cos \alpha + \sin \alpha = 0$
    have h8 : sin α = -cos α := by linarith
    have h9 : cos α ≠ 0 := by
      by_contra h10
      have h11 : sin α = 0 := by
        linarith [h8, h10]
      have h12 : sin α ^ 2 + cos α ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq α
      rw [h11, h10] at h12
      nlinarith
    have h10 : tan α = -1 := by
      rw [tan_eq_sin_div_cos]
      have h11 : sin α = -cos α := h8
      have h12 : cos α ≠ 0 := h9
      field_simp [h12]
      <;> nlinarith [h8]
    exact h10