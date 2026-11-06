import Mathlib

theorem algebra_254939 (θ : ℝ) (h₀ : Real.sin θ + Real.cos θ = 7 / 5) (h₁ : Real.tan θ < 1) :
    Real.sin θ = 3 / 5 := by

  have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ

  have h3 : Real.sin θ + Real.cos θ = 7 / 5 := h₀
  have h4 : (Real.sin θ + Real.cos θ) ^ 2 = (7 / 5) ^ 2 := by
    rw [h3]

  have h5 : Real.sin θ * Real.cos θ = 12 / 25 := by
    have h6 : (Real.sin θ + Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 + 2 * (Real.sin θ * Real.cos θ) := by ring
    rw [h6] at h4
    have h7 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := h2
    nlinarith

  have h8 : Real.cos θ = 7 / 5 - Real.sin θ := by
    linarith

  rw [h8] at h5

  have h9 : 25 * Real.sin θ ^ 2 - 35 * Real.sin θ + 12 = 0 := by 
    nlinarith
  
  have h10 : (Real.sin θ - 3 / 5) * (Real.sin θ - 4 / 5) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.mp h10) with h11 h12
  
  · -- Real.sin θ - 3/5 = 0, so Real.sin θ = 3/5
    have : Real.sin θ = 3 / 5 := by linarith
    linarith
  
  · -- Real.sin θ - 4/5 = 0, so Real.sin θ = 4/5
    have h13 : Real.sin θ = 4 / 5 := by linarith
  
    have h14 : Real.cos θ = 3 / 5 := by
      linarith [h₀, h13]
  
    have h15 : Real.tan θ = 4 / 3 := by
      rw [Real.tan_eq_sin_div_cos, h13, h14]
      all_goals norm_num
  
    rw [h15] at h₁
    norm_num at h₁