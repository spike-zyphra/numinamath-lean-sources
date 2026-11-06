import Mathlib

theorem algebra_273510 (α β : ℝ) (h₁ : Real.sin (α + β) = 1 / 2) (h₂ : Real.sin (α - β) = 1 / 3) :
    Real.tan α * 1 / Real.tan β = 5 := by
  have h3 : Real.sin α * Real.cos β + Real.cos α * Real.sin β = 1 / 2 := by
    rw [Real.sin_add] at h₁
    linarith
  have h4 : Real.sin α * Real.cos β - Real.cos α * Real.sin β = 1 / 3 := by
    rw [Real.sin_sub] at h₂
    linarith
  have h5 : Real.sin α * Real.cos β = 5 / 12 := by
    linarith
  have h6 : Real.cos α * Real.sin β = 1 / 12 := by
    linarith
  have htan : Real.tan α * 1 / Real.tan β = (Real.sin α * Real.cos β) / (Real.cos α * Real.sin β) := by 
    field_simp [Real.tan_eq_sin_div_cos]
    <;> ring_nf <;> field_simp [Real.tan_eq_sin_div_cos] <;> ring
  rw [htan]
  rw [h5, h6]
  all_goals norm_num