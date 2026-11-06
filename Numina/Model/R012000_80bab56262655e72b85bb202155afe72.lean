import Mathlib

theorem algebra_165419 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : α + β ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.tan (α + β) = (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h3 : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h₀₁, h₀₂, Real.pi_pos]
    · linarith [h₀₁, h₀₂, Real.pi_pos]
  have h4 : Real.sin α > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [h₀₁, h₀₂, Real.pi_pos]
    linarith [h₀₁, h₀₂, Real.pi_pos]
  have h5 : Real.cos β > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h₁₁, h₁₂, Real.pi_pos]
    · linarith [h₁₁, h₁₂, Real.pi_pos]
  have h6 : Real.sin β > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [h₁₁, h₁₂, Real.pi_pos]
    linarith [h₁₁, h₁₂, Real.pi_pos]
  have h7 : Real.cos (α + β) > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h₂₁, h₂₂, Real.pi_pos]
    · linarith [h₂₁, h₂₂, Real.pi_pos]
  have h8 : Real.sin (α + β) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [h₂₁, h₂₂, Real.pi_pos]
    linarith [h₂₁, h₂₂, Real.pi_pos]
  have htan1 : Real.tan (α + β) = Real.sin (α + β) / Real.cos (α + β) := by 
    rw [Real.tan_eq_sin_div_cos]
  have h9 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by 
    rw [Real.sin_add]
  have h10 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
    rw [Real.cos_add]
  have htanα : Real.tan α = Real.sin α / Real.cos α := by 
    rw [Real.tan_eq_sin_div_cos]
  have htanβ : Real.tan β = Real.sin β / Real.cos β := by 
    rw [Real.tan_eq_sin_div_cos]
  rw [htan1, htanα, htanβ]
  have h11 : Real.cos α ≠ 0 := by
    linarith [h3]
  have h12 : Real.cos β ≠ 0 := by 
    linarith [h5]
  have h14 : Real.cos (α + β) ≠ 0 := by
    linarith [h7]
  rw [h9, h10]
  field_simp [h11, h12, h14]
  ring