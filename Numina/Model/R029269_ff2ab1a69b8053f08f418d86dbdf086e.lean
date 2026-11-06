import Mathlib

theorem algebra_106724 (α β γ : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : γ ∈ Set.Ioo 0 (Real.pi / 2)) (h₃ : α + β + γ = Real.pi)
    (h₄ : 4 * Real.sin α + 5 * Real.cos β = 6) (h₅ : 5 * Real.sin β + 4 * Real.cos α = 5) :
    γ = Real.pi / 6 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h6 : 0 < Real.sin α := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h7 : 0 < Real.sin β := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h8 : 0 < Real.cos α := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h9 : 0 < Real.cos β := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h10 : (4 * Real.sin α + 5 * Real.cos β) ^ 2 + (5 * Real.sin β + 4 * Real.cos α) ^ 2 = 61 := by
    nlinarith [h₄, h₅]
  have h11 : (Real.sin α) ^ 2 + (Real.cos α) ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h12 : (Real.sin β) ^ 2 + (Real.cos β) ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have h13 : Real.sin α * Real.cos β + Real.sin β * Real.cos α = 1 / 2 := by
    nlinarith [h10, h11, h12, mul_pos h6 h7, mul_pos h6 h8, mul_pos h7 h8, mul_pos h7 h9, mul_pos h6 h9, mul_pos h8 h9]
  have h14 : Real.sin (α + β) = 1 / 2 := by
    rw [Real.sin_add]
    linarith [h13]
  have h15 : α + β = Real.pi - γ := by
    linarith [h₃]
  have h16 : Real.sin (α + β) = Real.sin (Real.pi - γ) := by
    rw [show α + β = Real.pi - γ by linarith [h₃]]
  have h17 : Real.sin (Real.pi - γ) = Real.sin γ := by
    rw [Real.sin_pi_sub]
  have h18 : Real.sin γ = 1 / 2 := by
    linarith [h16, h17, h14]
  -- Since $\gamma$ is acute and $\sin \gamma = 1/2$, $\gamma = \pi/6$
  have h19 : γ = Real.arcsin (Real.sin γ) := by
    rw [Real.arcsin_sin]
    all_goals
      linarith [h₂₁, h₂₂]
  have h20 : Real.arcsin (Real.sin γ) = Real.arcsin (1 / 2) := by
    rw [h18]
  have h21 : Real.arcsin (1 / 2) = Real.pi / 6 := by
    have h1 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    have h2 : Real.arcsin (Real.sin (Real.pi / 6)) = Real.pi / 6 := by
      apply Real.arcsin_sin
      all_goals
        linarith [Real.pi_pos]
    rw [h1] at h2
    linarith
  rw [h19, h20, h21]