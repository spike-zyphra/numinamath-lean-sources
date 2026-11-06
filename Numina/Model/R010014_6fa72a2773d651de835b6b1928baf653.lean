import Mathlib

theorem algebra_20209 {x y : ℝ} (h₀ : x - y = 6) (h₁ : x ^ 2 + y ^ 2 = 24) :
    x ^ 3 - y ^ 3 = 108 := by 
  have h2 : x * y = -6 := by 
    have h : (x - y) ^ 2 = 36 := by
      rw [h₀]
      norm_num
    have h3 : (x - y) ^ 2 = x^2 - 2 * (x * y) + y^2 := by
      ring
    rw [h3] at h
    nlinarith 
  have h3 : x^3 - y^3 = (x - y) * (x^2 + y^2 + (x * y)) := by 
    ring
  rw [h3, h₀, h₁, h2]
  all_goals norm_num