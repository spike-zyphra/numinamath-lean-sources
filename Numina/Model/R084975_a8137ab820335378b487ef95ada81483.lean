import Mathlib

theorem algebra_209175 {x y : ℝ} (h₁ : Real.sin x - Real.sin y = Real.sqrt (1008 / 1009)) (h₂ : Real.cos x - Real.cos y = 1) :
    Real.cos (x - y) = 1 / 2018 := by
  have h3 : (Real.sin x - Real.sin y) ^ 2 = 1008 / 1009 := by
    rw [h₁]
    have h4 : (Real.sqrt (1008 / 1009)) ^ 2 = 1008 / 1009 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    linarith

  have h5 : (Real.cos x - Real.cos y) ^ 2 = 1 := by 
    rw [h₂]
    norm_num

  have h6 : (Real.sin x - Real.sin y) ^ 2 + (Real.cos x - Real.cos y) ^ 2 = 1008 / 1009 + 1 := by 
    linarith [h3, h5]

  have h7 : (Real.sin x - Real.sin y) ^ 2 + (Real.cos x - Real.cos y) ^ 2 = 
      (Real.sin x ^ 2 + Real.cos x ^ 2) + (Real.sin y ^ 2 + Real.cos y ^ 2) - 2 * (Real.sin x * Real.sin y + Real.cos x * Real.cos y) := by
    ring

  have h8 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h9 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y

  have h14 : Real.sin x * Real.sin y + Real.cos x * Real.cos y = 1 / 2018 := by 
    nlinarith [h6, h7, h8, h9]

  have h15 : Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by 
    rw [Real.cos_sub]

  linarith [h14, h15]