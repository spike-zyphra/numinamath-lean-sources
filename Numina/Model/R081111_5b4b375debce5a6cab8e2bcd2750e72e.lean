import Mathlib

theorem algebra_216274 (x : ℝ) (hx : x > 0) (h : (1 + x / 100) * (1 - x / 100) = (1 - 36 / 100)) :
    x = 60 := by 
  have h1 : (1 + x / 100) * (1 - x / 100) = 1 - x ^ 2 / 10000 := by 
    ring
  rw [h1] at h
  have h2 : x ^ 2 = 3600 := by
    nlinarith
  have h4 : x = 60 := by
    nlinarith [h2, show x > 0 by linarith]
  exact h4