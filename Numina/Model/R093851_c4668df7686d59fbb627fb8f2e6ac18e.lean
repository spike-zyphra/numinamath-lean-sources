import Mathlib

open Finset

theorem algebra_18602 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, f x y = (x + y) / 2) :
    f 3 (f 6 8) = 5 := by
  have h1 : f 6 8 = 7 := by 
    rw [hf]
    norm_num
  rw [h1]
  rw [hf]
  norm_num