import Mathlib

theorem algebra_147923 (f : ℝ → ℝ) (hf : ∀ x, f x = -1/2 * 5^x + 4) :
    f 0 = 7/2 := by
  have h0 := hf 0
  rw [h0]
  norm_num