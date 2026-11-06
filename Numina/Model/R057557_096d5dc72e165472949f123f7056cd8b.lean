import Mathlib

theorem calculus_23184 (θ : Real) (h : Real.sin θ ^ 2 + Real.sin θ = 1) :
    Real.cos θ ^ 4 + Real.cos θ ^ 2 = 1 := by 
  have h2 : Real.cos θ ^ 2 = Real.sin θ := by
    have hsin_sq : Real.sin θ ^ 2 = 1 - Real.sin θ := by 
      linarith 
    have hsin : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [hsin_sq] at hsin 
    linarith
  have hcos_sq : Real.cos θ ^ 4 = (Real.sin θ)^2 := by 
    calc 
      Real.cos θ ^ 4 = (Real.cos θ ^ 2)^2 := by ring
      _ = (Real.sin θ)^2 := by rw [h2]
  calc 
    Real.cos θ ^ 4 + Real.cos θ ^ 2 = (Real.sin θ)^2 + Real.sin θ := by 
      rw [hcos_sq, h2]
    _ = 1 := by 
      linarith [h]