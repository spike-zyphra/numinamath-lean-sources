import Mathlib

theorem algebra_239169 : Real.sqrt ((145.5^2 - 96.5^2) / (193.5^2 - 31.5^2)) = 77 / 135 := by
  have h1 : (145.5^2 - 96.5^2 : ℝ) / (193.5^2 - 31.5^2 : ℝ) = (77 / 135 : ℝ) ^ 2 := by
    norm_num
  rw [h1]
  rw [Real.sqrt_sq]
  all_goals norm_num
  all_goals norm_num