import Mathlib

theorem algebra_327360 {x y : ℝ} (h₁ : x / (2 ^ 10 + 5 ^ 3) + y / (2 ^ 10 + 6 ^ 3) = 1)
    (h₂ : x / (3 ^ 10 + 5 ^ 3) + y / (3 ^ 10 + 6 ^ 3) = 1) :
    x + y = 2 ^ 10 + 3 ^ 10 + 5 ^ 3 + 6 ^ 3 := by
  norm_num at h₁ h₂
  linarith