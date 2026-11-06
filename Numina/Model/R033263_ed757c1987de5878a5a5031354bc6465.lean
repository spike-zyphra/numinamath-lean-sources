import Mathlib

theorem algebra_22238 {f : ℝ → ℝ} (hf : f (-2) = 3) :
    ∃ (x y : ℝ), y = f (2 * x + 1) + 3 := by
  use (-3 / 2)
  use 6
  rw [show 2 * (-3 / 2 : ℝ) + 1 = -2 by norm_num]
  rw [hf]
  all_goals norm_num