import Mathlib

theorem algebra_152124 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f (-x + 2) = -f (x - 2)) (h : ∀ x, f x = x^3 + a * x^2 + b * x + 2) :
    f 1 = 4 := by 
  have eq1 := hf 2
  have eq2 : f 0 = 2 := by
    specialize h 0
    norm_num at h ⊢
    linarith
  have eq3 : f 0 = -f 0 := by
    specialize hf 2
    norm_num at hf
    linarith
  rw [eq2] at eq3
  all_goals linarith