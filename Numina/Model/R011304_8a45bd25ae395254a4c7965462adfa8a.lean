import Mathlib

theorem algebra_12219 {α β : ℝ} (hα : α ∈ Set.Ioo 0 Real.pi) (hβ : β ∈ Set.Ioo 0 Real.pi)
    (hroots : Real.tan α + Real.tan β = -3 ∧ Real.tan α * Real.tan β = 1) :
    Real.cos (α - β) = 2 / 3 := by
  rcases hα with ⟨hα1, hα2⟩
  rcases hβ with ⟨hβ1, hβ2⟩
  have h1 : Real.sin α > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : Real.sin β > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hcosα1 : Real.cos α ≠ 0 := by
    by_contra hcos
    have htanα : Real.tan α = 0 := by 
      rw [Real.tan_eq_sin_div_cos]
      rw [hcos]
      norm_num
    rw [htanα] at hroots
    nlinarith [show 0 < (Real.pi : ℝ) by linarith [Real.pi_pos]]
  have hcosβ1 : Real.cos β ≠ 0 := by 
    by_contra hcos
    have htanβ : Real.tan β = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      rw [hcos]
      norm_num
    rw [htanβ] at hroots
    nlinarith [show 0 < (Real.pi : ℝ) by linarith [Real.pi_pos]]
  have h3 : Real.tan α + Real.tan β = -3 := hroots.1
  have h4 : Real.tan α * Real.tan β = 1 := hroots.2
  have htanα : Real.tan α = Real.sin α / Real.cos α := by 
    rw [Real.tan_eq_sin_div_cos]
  have htanβ : Real.tan β = Real.sin β / Real.cos β := by 
    rw [Real.tan_eq_sin_div_cos]
  rw [htanα] at h3 h4
  rw [htanβ] at h3 h4
  -- Rewrite tangent equations to clear denominators
  have h_eq1 : Real.sin α * Real.cos β + Real.cos α * Real.sin β = -3 * (Real.cos α * Real.cos β) := by
    field_simp [hcosα1, hcosβ1] at h3 ⊢
    nlinarith 
  have h_eq2 : Real.sin α * Real.sin β = Real.cos α * Real.cos β := by 
    field_simp [hcosα1, hcosβ1] at h4 ⊢
    nlinarith 
  have h3 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by 
    rw [Real.cos_sub]
  have h8 : Real.cos α * Real.cos β = 1 / 3 := by
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, h_eq1, h_eq2, mul_pos h1 h2]
  rw [h3]
  nlinarith [h_eq2, h8]