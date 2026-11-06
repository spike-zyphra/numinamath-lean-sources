import Mathlib

theorem algebra_7303 {a b c d : ℝ} (h₀ : a/3 + b/5 + c/9 + d/17 = 1)
    (h₁ : a/4 + b/6 + c/10 + d/18 = 1/2) (h₂ : a/5 + b/7 + c/11 + d/19 = 1/3)
    (h₃ : a/6 + b/8 + c/12 + d/20 = 1/4) :
    a/10 + b/12 + c/16 + d/24 = 1/36 := by 
  linarith