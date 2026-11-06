import Mathlib

theorem algebra_13106 (d f t : ℝ) (h₀ : d = 100 * (1 + 10 / 100 * t)) (h₁ : f = 150 * (1 + 5 / 100 * t)) :
    d = f → t = 20 := by 
  intro h_eq
  rw [h₀, h₁] at h_eq
  linarith