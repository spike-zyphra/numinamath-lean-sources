import Mathlib

theorem algebra_87611 {f : ℝ → ℝ} (hf : ∀ x y, 0 < x → 0 < y → f (x * y) = f x / y)
    (h : f 500 = 3) : f 600 = 5 / 2 := by 
  have h1 : f 600 = f (500 * (6 / 5 : ℝ)) := by
    norm_num
  have h2 := hf 500 (6 / 5 : ℝ) (by norm_num) (by norm_num)
  rw [h1]
  rw [h2]
  rw [h]
  norm_num