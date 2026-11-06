import Mathlib

theorem algebra_288448 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f (2 * x - 3) - 2 * f (3 * x - 10) + f (x - 3) = 28 - 6 * x) :
    f 4 = 8 := by 
  have eq1 := hf 2
  norm_num at eq1
  have h1 : f (-4) = -f 4 := hodd 4
  have h2 : f (-1) = -f 1 := hodd 1
  rw [h1, h2] at eq1
  linarith