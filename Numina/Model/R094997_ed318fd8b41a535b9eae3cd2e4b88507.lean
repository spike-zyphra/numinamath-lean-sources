import Mathlib

theorem algebra_5033 (θ : ℝ) (h : Real.sin (2 * θ) = 21 / 25) (h' : Real.cos θ > Real.sin θ) :
    Real.cos θ - Real.sin θ = 2 / 5 := by
  have h1 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by
    rw [Real.sin_two_mul]

  rw [h1] at h
  
  have h2 : Real.sin θ * Real.cos θ = 21 / 50 := by 
    linarith
  
  have h3 : (Real.cos θ - Real.sin θ) ^ 2 = 4 / 25 := by
    have h4 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    calc 
      (Real.cos θ - Real.sin θ) ^ 2 = Real.cos θ ^ 2 + Real.sin θ ^ 2 - 2 * (Real.sin θ * Real.cos θ) := by 
        ring
      _ = 1 - 2 * (Real.sin θ * Real.cos θ) := by 
        rw [h4]
      _ = 1 - 2 * (21 / 50) := by 
        rw [h2]
      _ = 4 / 25 := by 
        norm_num
  
  have h4 : Real.cos θ - Real.sin θ > 0 := by 
    linarith
  
  have h5 : Real.cos θ - Real.sin θ = 2 / 5 := by 
    nlinarith [h3, h4]

  exact h5