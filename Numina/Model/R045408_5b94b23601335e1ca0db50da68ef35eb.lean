import Mathlib

theorem algebra_195254 (α β : ℝ) (h₀ : 0 < α) (h₁ : α < Real.pi / 2) (h₂ : 0 < β)
    (h₃ : β < Real.pi / 2) (h₄ : 3 * (Real.sin α) ^ 2 + 2 * (Real.sin β) ^ 2 = 1)
    (h₅ : 3 * Real.sin (2 * α) - 2 * Real.sin (2 * β) = 0) :
    α + 2 * β = Real.pi / 2 := by

  have h6 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
    rw [Real.sin_two_mul]

  have h7 : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := by
    rw [Real.sin_two_mul]

  rw [h6, h7] at h₅

  have h8 : 3 * (Real.sin α) * (Real.cos α) = 2 * (Real.sin β) * (Real.cos β) := by
    nlinarith

  have h9 : Real.sin α > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have h10 : Real.sin β > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have hcos : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have hcos' : Real.cos β > 0 := by 
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have h11 : (Real.sin β)^2 = 1 / 3 := by 
    have hcosα : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by 
      linarith [Real.sin_sq_add_cos_sq α]
    have hcosβ : Real.cos β ^ 2 = 1 - Real.sin β ^ 2 := by 
      linarith [Real.sin_sq_add_cos_sq β]
    nlinarith [h₄, h8, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
      mul_pos h9 hcos, mul_pos h10 hcos']

  by_cases h15 : α + 2 * β < Real.pi / 2
  · -- Show contradiction
    have h16 : α < Real.pi / 2 - 2 * β := by linarith
    have h17 : Real.sin α < Real.sin (Real.pi / 2 - 2 * β) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos]
    have h18 : Real.sin (Real.pi / 2 - 2 * β) = Real.cos (2 * β) := by 
      rw [Real.sin_pi_div_two_sub]
    have h19 : Real.sin α < Real.cos (2 * β) := by 
      linarith [h17, h18]
    have h20 : Real.cos (2 * β) = 1 - 2 * (Real.sin β) ^ 2 := by 
      rw [Real.cos_two_mul, Real.sin_sq]
      ring
    nlinarith [h19, h20, h11, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, h9, hcos', Real.pi_pos]

  by_cases h17 : α + 2 * β > Real.pi / 2
  · -- Show contradiction
    have h18 : α > Real.pi / 2 - 2 * β := by linarith
    have h19 : Real.sin α > Real.sin (Real.pi / 2 - 2 * β) := by 
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos]
    have h20 : Real.sin (Real.pi / 2 - 2 * β) = Real.cos (2 * β) := by 
      rw [Real.sin_pi_div_two_sub]
    have h21 : Real.sin α > Real.cos (2 * β) := by 
      linarith [h19, h20]
    have h22 : Real.cos (2 * β) = 1 - 2 * (Real.sin β) ^ 2 := by 
      rw [Real.cos_two_mul, Real.sin_sq]
      ring
    nlinarith [h21, h22, h11, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, h9, hcos', Real.pi_pos]

  linarith