import Mathlib

theorem algebra_237893 {b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (h0 : f 0 + f 1 = 1 / 2) : f (1 / 2) = 0 := by
  have h1 : f 0 = c := by 
    rw [hf]
    all_goals norm_num
  have h2 : f 1 = 1 ^ 2 + b * (1) + c := by 
    apply hf
  rw [h1, h2] at h0
  have h3 : f (1 / 2) = (1 / 2) ^ 2 + b * (1 / 2) + c := by 
    apply hf
  linarith [h3, h0]