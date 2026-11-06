import Mathlib

theorem algebra_2207 {x : ℚ} (f : ℚ → ℚ) (hf : ∀ x, f x = x ^ 2 + 1) : f (f (-1)) = 5 := by 
  have h1 : f (-1) = 2 := by
    rw [hf]
    norm_num
  rw [h1]
  rw [hf]
  norm_num