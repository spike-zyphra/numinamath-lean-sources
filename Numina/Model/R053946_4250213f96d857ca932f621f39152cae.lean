import Mathlib

open Finset

theorem algebra_223436 {f : ℕ → ℕ → ℝ}
    (hf : ∀ a b, f a b = ((a + 1) * (b - 1)) / (a * b) - 1) :
    f 43 47 * 43 * 47 = 3 := by 
  have h1 : f 43 47 = ((43 + 1 : ℝ) * (47 - 1 : ℝ)) / ((43 : ℝ) * (47 : ℝ)) - 1 := by 
    apply hf 
  rw [h1]
  norm_num