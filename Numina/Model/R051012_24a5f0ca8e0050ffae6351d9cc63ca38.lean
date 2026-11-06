import Mathlib

open Finset

theorem algebra_263138 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, f x y = (x + y) / (x * y)) :
    f 3 6 = 1 / 2 := by
  have h1 : f 3 6 = (3 + 6) / (3 * 6) := hf 3 6
  rw [h1]
  norm_num