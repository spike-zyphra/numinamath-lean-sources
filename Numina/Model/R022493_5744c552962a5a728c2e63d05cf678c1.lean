import Mathlib

theorem algebra_114774 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : Real.sin α ^ 2 + Real.sin β ^ 2 = Real.sin (α + β)) :
    α + β = Real.pi / 2 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h3 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]
  rw [h3] at h₂
  by_cases h : α + β < Real.pi / 2
  · -- Assume $\alpha + \beta < \frac{\pi}{2}$
    have h4 : α < Real.pi / 2 - β := by
      linarith
    have h5 : Real.sin α < Real.cos β := by
      have h6 : α < Real.pi / 2 - β := h4
      have h7 : Real.sin α < Real.sin (Real.pi / 2 - β) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [h₀₁, h₀₂, h₁₁, h₁₂, Real.pi_pos]
      have h8 : Real.sin (Real.pi / 2 - β) = Real.cos β := by 
        rw [Real.sin_pi_div_two_sub]
      linarith [h8]
    have h8 : Real.sin β < Real.cos α := by 
      have h9 : β < Real.pi / 2 - α := by 
        linarith
      have h10 : Real.sin β < Real.sin (Real.pi / 2 - α) := by 
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [h₀₁, h₀₂, h₁₁, h₁₂, Real.pi_pos]
      have h11 : Real.sin (Real.pi / 2 - α) = Real.cos α := by
        rw [Real.sin_pi_div_two_sub]
      linarith [h11]
    nlinarith [Real.sin_pos_of_pos_of_lt_pi h₀₁ (show α < Real.pi by linarith [Real.pi_gt_three, h₀₂, h₁₂]), 
          Real.sin_pos_of_pos_of_lt_pi h₁₁ (show β < Real.pi by linarith [Real.pi_gt_three, h₀₂, h₁₂]), 
          Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          Real.sin_pos_of_pos_of_lt_pi h₀₁ (show α < Real.pi by linarith), 
          Real.sin_pos_of_pos_of_lt_pi h₁₁ (show β < Real.pi by linarith)]
  by_cases h' : α + β > Real.pi / 2
  · -- Assume $\alpha + \beta > \frac{\pi}{2}$
    have h4 : α > Real.pi / 2 - β := by 
      linarith
    have h5 : Real.sin α > Real.cos β := by 
      have h6 : α > Real.pi / 2 - β := h4
      have h7 : Real.sin α > Real.sin (Real.pi / 2 - β) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals 
          linarith [h₀₁, h₀₂, h₁₁, h₁₂, Real.pi_pos]
      have h8 : Real.sin (Real.pi / 2 - β) = Real.cos β := by
        rw [Real.sin_pi_div_two_sub]
      linarith [h8]
    have h8 : Real.sin β > Real.cos α := by 
      have h9 : β > Real.pi / 2 - α := by 
        linarith
      have h10 : Real.sin β > Real.sin (Real.pi / 2 - α) := by 
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals 
          linarith [h₀₁, h₀₂, h₁₁, h₁₂, Real.pi_pos]
      have h11 : Real.sin (Real.pi / 2 - α) = Real.cos α := by 
        rw [Real.sin_pi_div_two_sub]
      linarith [h11]
    nlinarith [Real.sin_pos_of_pos_of_lt_pi h₀₁ (show α < Real.pi by linarith [Real.pi_gt_three, h₀₂, h₁₂]), 
          Real.sin_pos_of_pos_of_lt_pi h₁₁ (show β < Real.pi by linarith [Real.pi_gt_three, h₀₂, h₁₂]), 
          Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          Real.sin_pos_of_pos_of_lt_pi h₀₁ (show α < Real.pi by linarith), 
          Real.sin_pos_of_pos_of_lt_pi h₁₁ (show β < Real.pi by linarith)]
  linarith