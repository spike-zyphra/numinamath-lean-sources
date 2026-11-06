import Mathlib

theorem algebra_20016 {x : ℤ} (h : x^2 = 225) : x = -15 ∨ x = 15 := by
  have h1 : x^2 - 225 = 0 := by 
    linarith [h]

  have h2 : x^2 - 225 = (x - 15) * (x + 15) := by 
    ring

  rw [h2] at h1
  
  cases' (mul_eq_zero.mp h1) with h3 h4
  
  · 
    right
    linarith
  
  · 
    left
    linarith