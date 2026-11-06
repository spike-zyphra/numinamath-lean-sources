import Mathlib

open Finset

theorem algebra_95552 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, f x y = x - 1 / y) :
    (f (f 1 2) 3) - (f 1 (f 2 3)) = -7 / 30 := by
  have h1 : f 1 2 = 1/2 := by 
    rw [hf]
    norm_num
  have h2 : f (f 1 2) 3 = 1/6 := by
    rw [h1]
    rw [hf]
    norm_num
  have h3 : f 2 3 = 5/3 := by 
    rw [hf]
    norm_num
  have h4 : f 1 (f 2 3) = 2/5 := by 
    rw [h3]
    rw [hf]
    norm_num
  rw [h2, h4]
  norm_num