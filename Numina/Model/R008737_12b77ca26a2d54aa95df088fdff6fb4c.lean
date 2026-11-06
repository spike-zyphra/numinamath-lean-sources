import Mathlib

theorem algebra_14165 {a b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 7 + b * x ^ 3 + c * x - 5)
    (h : f (-7) = 7) : f 7 = -17 := by 
  have eq1 : f (-7) = a * (-7) ^ 7 + b * (-7) ^ 3 + c * (-7) - 5 := by 
    apply hf
  have eq2 : f 7 = a * 7 ^ 7 + b * 7 ^ 3 + c * 7 - 5 := by 
    apply hf
  rw [eq1] at h
  rw [eq2] at *
  ring_nf at h ⊢
  linarith