import Mathlib

theorem algebra_248855 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : Real.sin (α + β) = Real.sin α ^ 2 + Real.sin β ^ 2) :
    α + β = Real.pi / 2 := by
  rcases h₀ with ⟨hα1, hα2⟩
  rcases h₁ with ⟨hβ1, hβ2⟩
  have h3 : Real.sin α > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi 
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : Real.sin β > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi 
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h5 : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo 
    constructor <;> linarith [Real.pi_pos]
  have h6 : Real.cos β > 0 := by 
    apply Real.cos_pos_of_mem_Ioo 
    constructor <;> linarith [Real.pi_pos]
  have h7 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by 
    rw [Real.sin_add]
  rw [h7] at h₂
  by_cases h : α + β < Real.pi / 2
  · -- Assume α + β < π/2.
    have h8 : Real.sin α < Real.cos β := by
      have h9 : α < Real.pi / 2 - β := by linarith 
      have h10 : Real.sin α < Real.sin (Real.pi / 2 - β) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      have h11 : Real.sin (Real.pi / 2 - β) = Real.cos β := by 
        rw [Real.sin_pi_div_two_sub]
      nlinarith [h11, h10]
    have h9 : Real.sin β < Real.cos α := by
      have h10 : β < Real.pi / 2 - α := by linarith 
      have h11 : Real.sin β < Real.sin (Real.pi / 2 - α) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      have h12 : Real.sin (Real.pi / 2 - α) = Real.cos α := by 
        rw [Real.sin_pi_div_two_sub]
      nlinarith [h12, h11]
    nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, sq_pos_of_pos h5, sq_pos_of_pos h6, 
          Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          mul_pos h3 h4, mul_pos h3 h5, mul_pos h3 h6, 
          mul_pos h4 h5, mul_pos h4 h6, mul_pos h5 h6
    ]
  · -- Case where α + β ≥ π/2
    by_cases h : α + β > Real.pi / 2 
    · -- Assume α + β > π/2.
      have h12 : Real.sin α > Real.cos β := by 
          have h13 : α > Real.pi / 2 - β := by linarith 
          have h14 : Real.sin α > Real.sin (Real.pi / 2 - β) := by 
            apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals linarith [Real.pi_pos]
          have h15 : Real.sin (Real.pi / 2 - β) = Real.cos β := by 
            rw [Real.sin_pi_div_two_sub]
          nlinarith [h15, h14]
      have h13 : Real.sin β > Real.cos α := by
        have h14 : β > Real.pi / 2 - α := by linarith 
        have h15 : Real.sin β > Real.sin (Real.pi / 2 - α) := by 
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [Real.pi_pos]
        have h16 : Real.sin (Real.pi / 2 - α) = Real.cos α := by 
          rw [Real.sin_pi_div_two_sub]
        nlinarith [h16, h15]
      nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, sq_pos_of_pos h5, sq_pos_of_pos h6, 
            Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
            mul_pos h3 h4, mul_pos h3 h5, mul_pos h3 h6, 
            mul_pos h4 h5, mul_pos h4 h6, mul_pos h5 h6
        ]
    · -- Now we need to show it's exactly equal
      linarith