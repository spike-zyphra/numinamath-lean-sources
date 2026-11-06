import Mathlib

theorem algebra_41808 {a b : ℝ} (h1 : a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4 = 900) (h2 : a ^ 2 + a * b + b ^ 2 = 45) :
    2 * a * b = 25 := by 
  have eq1 : a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4 = (a ^ 2 + a * b + b ^ 2) * (a ^ 2 - a * b + b ^ 2) := by 
    ring
  rw [eq1] at h1 
  rw [h2] at h1 
  have h3 : a ^ 2 - a * b + b ^ 2 = 20 := by 
    nlinarith 
  have h4 : 2 * a * b = 25 := by
    nlinarith 
  exact h4