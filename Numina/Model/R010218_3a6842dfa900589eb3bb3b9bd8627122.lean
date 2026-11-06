import Mathlib

theorem algebra_9211
    {f : ℝ → ℝ}
    (hf : ∀ x, f x = (x + 3) / (x - 6)) :
    f 3 = -2 := by
  rw [hf]
  norm_num