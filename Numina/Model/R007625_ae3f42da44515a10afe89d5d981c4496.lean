import Mathlib

  theorem algebra_14201 {f : ℝ → ℝ} (hf : ∀ x, f x = 8 * x ^ 3 - 6 * x ^ 2 - 4 * x + 5) :
    f (-2) = -75 := by
  rw [hf]
  norm_num