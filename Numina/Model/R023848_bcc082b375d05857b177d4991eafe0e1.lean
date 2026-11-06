import Mathlib

open Finset

theorem algebra_15463 {f : ℕ → ℝ} (hf : ∀ n, f n = (n - f (n - 1)) / (1 - n * f (n - 1))) (hf0 : f 0 = 1) :
    f 999 = 1 := by
  have eq1 := hf 0
  simp at eq1
  linarith