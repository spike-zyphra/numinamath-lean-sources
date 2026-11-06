import Mathlib

open Finset

theorem algebra_22026 {f : ℝ → ℝ → ℝ} (hf : f = fun A B => (A + B) / 2) :
    f (f 3 5) 8 = 6 := by 
  rw [hf]
  norm_num [hf]