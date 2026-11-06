import Mathlib

theorem algebra_21812 (b c : ℝ) (f : ℝ → ℝ) (hf : ∀x, f x = x ^ 2 + b * x + c) (h1: 3 = f 2) (h2: 3 = f 4) :
    c = 11 := by 
  have eq1 : 3 = 2^2 + b * 2 + c := by 
    rw [hf] at h1
    linarith
  have eq2 : 3 = 4^2 + b * 4 + c := by 
    rw [hf] at h2
    linarith 
  linarith