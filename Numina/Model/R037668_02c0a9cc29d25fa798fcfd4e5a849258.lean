import Mathlib

theorem algebra_259599 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : 3 * (Real.sin α)^2 + 2 * (Real.sin β)^2 = 1) (h₃ : 3 * Real.sin (2 * α) - 2 * Real.sin (2 * β) = 0) :
    α + 2 * β = Real.pi / 2 := by
  rcases h₀ with ⟨h01, h02⟩
  rcases h₁ with ⟨h11, h12⟩
  have h4 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
    rw [Real.sin_two_mul]
  have h5 : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := by
    rw [Real.sin_two_mul]
  rw [h4, h5] at h₃
  have h6 : 3 * (Real.sin α) * (Real.cos α) = 2 * (Real.sin β) * (Real.cos β) := by
    nlinarith
  have h7 : Real.sin β ^ 2 = (1 - 3 * Real.sin α ^ 2) / 2 := by
    nlinarith
  have h8 : Real.cos (2 * β) = 3 * Real.sin α ^ 2 := by
    have h9 : Real.cos (2 * β) = 1 - 2 * Real.sin β ^ 2 := by 
      rw [Real.cos_two_mul, Real.sin_sq]
      <;> nlinarith
    rw [h9, h7]
    all_goals
      nlinarith
  have h10 : Real.sin (2 * β) = 3 * Real.sin α * Real.cos α := by
    have h11 : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := by 
      rw [Real.sin_two_mul]
    rw [h11]
    nlinarith
  have h13 : Real.cos (α + 2 * β) = 0 := by
    have hcos : Real.cos (α + 2 * β) = Real.cos α * Real.cos (2 * β) - Real.sin α * Real.sin (2 * β) := by
      rw [Real.cos_add]
    rw [hcos, h8, h10]
    have h14 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by 
      linarith [Real.cos_sq_add_sin_sq α]
    nlinarith [ sq_nonneg (Real.sin α ^ 2 - 1), sq_nonneg (Real.cos α), Real.sin_sq_add_cos_sq α ]
  have h15 : α + 2 * β > 0 := by 
    linarith
  have h16 : α + 2 * β < 3 * Real.pi / 2 := by 
    nlinarith [ Real.pi_pos ]
  by_cases h : α + 2 * β < Real.pi / 2
  · -- Assume α + 2 * β < Real.pi / 2
    have hcos1 : Real.cos (α + 2 * β) > 0 := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor <;> linarith [ Real.pi_pos ]
    nlinarith
  by_cases h2 : α + 2 * β > Real.pi / 2 
  · -- Assume α + 2 * β > Real.pi / 2 
    have hcos2 : Real.cos (α + 2 * β) < 0 := by 
      have h11 : Real.pi / 2 < α + 2 * β := by linarith
      have h12 : α + 2 * β < 3 * Real.pi / 2 := by 
        nlinarith [ Real.pi_pos ]
      apply Real.cos_neg_of_pi_div_two_lt_of_lt 
      all_goals 
        nlinarith [ Real.pi_pos ]
    nlinarith
  linarith