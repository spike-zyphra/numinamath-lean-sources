import Mathlib

theorem algebra_263055 (α β : ℝ) (h₁ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₂ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₃ : (Real.sin α + Real.cos α) * (Real.sin β + Real.cos β) = 2) :
    (Real.sin (2 * α) + Real.cos (3 * β))^2 + (Real.sin (2 * β) + Real.cos (3 * α))^2 = 3 - 2 * Real.sqrt 2 := by
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h4 : (Real.sin α + Real.cos α) ^ 2 = 2 := by 
    nlinarith [sq_nonneg (Real.sin α - Real.cos α), sq_nonneg (Real.sin β - Real.cos β), 
      Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
      Real.sin_pos_of_pos_of_lt_pi h₁₁ (show α < Real.pi by linarith [h₁₂, Real.pi_pos]), 
      Real.sin_pos_of_pos_of_lt_pi h₂₁ (show β < Real.pi by linarith [h₂₂, Real.pi_pos]), 
      sq_nonneg (Real.sin α + Real.cos α - Real.sqrt 2), sq_nonneg (Real.sin β + Real.cos β - Real.sqrt 2), 
      Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have h5 : Real.sin α + Real.cos α = Real.sqrt 2 := by
    have h6 : (Real.sin α + Real.cos α) ^ 2 = 2 := h4
    have h7 : Real.sin α + Real.cos α ≥ 0 := by 
      have h8 : Real.sin α > 0 := Real.sin_pos_of_pos_of_lt_pi h₁₁ (show α < Real.pi by linarith [h₁₂, Real.pi_pos])
      have h9 : Real.cos α > 0 := by 
        apply Real.cos_pos_of_mem_Ioo
        constructor
        linarith [h₁₁, Real.pi_pos]
        linarith [h₁₂, Real.pi_pos]
      linarith
    have h10 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
    have h11 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h6, sq_nonneg (Real.sin α + Real.cos α - Real.sqrt 2)]
  have h8 : (Real.sin β + Real.cos β) ^ 2 = 2 := by 
    nlinarith [sq_nonneg (Real.sin α - Real.cos α), sq_nonneg (Real.sin β - Real.cos β), 
      Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
      Real.sin_pos_of_pos_of_lt_pi h₁₁ (show α < Real.pi by linarith [h₁₂, Real.pi_pos]), 
      Real.sin_pos_of_pos_of_lt_pi h₂₁ (show β < Real.pi by linarith [h₂₂, Real.pi_pos]), 
      sq_nonneg (Real.sin α + Real.cos α - Real.sqrt 2), sq_nonneg (Real.sin β + Real.cos β - Real.sqrt 2), 
      Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have h9 : Real.sin β + Real.cos β = Real.sqrt 2 := by 
    have h12 : (Real.sin β + Real.cos β) ^ 2 = 2 := h8
    have h13 : Real.sin β + Real.cos β ≥ 0 := by 
      have h14 : Real.sin β > 0 := Real.sin_pos_of_pos_of_lt_pi h₂₁ (show β < Real.pi by linarith [h₂₂, Real.pi_pos])
      have h15 : Real.cos β > 0 := by 
        apply Real.cos_pos_of_mem_Ioo
        constructor
        linarith [h₂₁, Real.pi_pos]
        linarith [h₂₂, Real.pi_pos]
      linarith
    have h15 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
    have h16 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h12, sq_nonneg (Real.sin β + Real.cos β - Real.sqrt 2)]
  have h12 : Real.sin α = Real.cos α := by 
    nlinarith [sq_nonneg (Real.sin α - Real.cos α), Real.sin_sq_add_cos_sq α, h5]
  have h13 : α = Real.pi / 4 := by 
    have h14 : Real.sin α = Real.cos α := h12
    have h15 : Real.sin α > 0 := Real.sin_pos_of_pos_of_lt_pi h₁₁ (show α < Real.pi by linarith [h₁₂, Real.pi_pos])
    have h16 : Real.cos α > 0 := by 
      apply Real.cos_pos_of_mem_Ioo
      constructor
      linarith [h₁₁, Real.pi_pos]
      linarith [h₁₂, Real.pi_pos]
    have h17 : Real.sin α = Real.cos α := h14
    have h18 : Real.sin α / Real.cos α = 1 := by
      field_simp [h16]
      linarith
    have h19 : Real.sin α / Real.cos α = Real.tan α := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [h19] at h18
    have h20 : Real.tan α = 1 := h18
    have h21 : α = Real.arctan (Real.tan α) := by 
      rw [Real.arctan_tan]
      all_goals 
        nlinarith [Real.pi_pos]
    rw [h20] at h21
    have h22 : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
    rw [h22] at h21
    linarith
  have h14 : Real.sin β = Real.cos β := by 
    nlinarith [sq_nonneg (Real.sin β - Real.cos β), Real.sin_sq_add_cos_sq β, h9]
  have h15 : β = Real.pi / 4 := by 
    have h16 : Real.sin β = Real.cos β := h14
    have h17 : Real.sin β > 0 := Real.sin_pos_of_pos_of_lt_pi h₂₁ (show β < Real.pi by linarith [h₂₂, Real.pi_pos])
    have h18 : Real.cos β > 0 := by 
      apply Real.cos_pos_of_mem_Ioo
      constructor
      linarith [h₂₁, Real.pi_pos]
      linarith [h₂₂, Real.pi_pos]
    have h19 : Real.sin β = Real.cos β := h16
    have h20 : Real.sin β / Real.cos β = 1 := by 
      field_simp [h18]
      linarith
    have h21 : Real.sin β / Real.cos β = Real.tan β := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [h21] at h20
    have h22 : Real.tan β = 1 := h20
    have h23 : β = Real.arctan (Real.tan β) := by 
      rw [Real.arctan_tan]
      all_goals 
        nlinarith [Real.pi_pos]
    rw [h22] at h23
    have h24 : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
    rw [h24] at h23
    linarith
  have h16 : Real.sin (2 * α) = 1 := by 
    rw [h13]
    have h17 : Real.sin (2 * (Real.pi / 4)) = 1 := by 
      have h18 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
      rw [h18]
      exact Real.sin_pi_div_two
    linarith
  have h17 : Real.sin (2 * β) = 1 := by 
    rw [h15]
    have h18 : Real.sin (2 * (Real.pi / 4)) = 1 := by 
      have h19 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
      rw [h19]
      exact Real.sin_pi_div_two
    linarith
  have h18 : Real.cos (3 * β) = -Real.sqrt 2 / 2 := by 
    rw [h15]
    have h19 : Real.cos (3 * (Real.pi / 4)) = -Real.sqrt 2 / 2 := by 
      have h20 : 3 * (Real.pi / 4) = Real.pi - (Real.pi / 4) := by ring
      rw [h20]
      rw [Real.cos_pi_sub]
      have h22 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      linarith
    linarith
  have h19 : Real.cos (3 * α) = -Real.sqrt 2 / 2 := by 
    rw [h13]
    have h20 : Real.cos (3 * (Real.pi / 4)) = -Real.sqrt 2 / 2 := by 
      have h21 : 3 * (Real.pi / 4) = Real.pi - (Real.pi / 4) := by ring
      rw [h21]
      rw [Real.cos_pi_sub]
      have h23 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      linarith
    linarith
  rw [h16, h18, h17, h19]
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]