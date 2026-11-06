import Mathlib

open Finset

theorem algebra_280228 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, f x y = (x + y) / (x * y)) :
    f (f 1 2) 3 = 1 := by
  have h1 : f 1 2 = (3 / 2 : ℝ) := by 
    rw [hf]
    norm_num
  rw [h1]
  rw [hf]
  norm_num