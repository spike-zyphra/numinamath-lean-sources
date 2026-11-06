import Mathlib

open Real

theorem algebra_12922 {f : ℝ → ℝ} (hf : f = fun x => (2 * x ^ 2 - 5 * x - 7) / (x ^ 2 - 4 * x + 1)) :
    ∃ x, f x = (2 * 3 ^ 2 - 5 * 3 - 7) / (3 ^ 2 - 4 * 3 + 1) := by 
  use 3
  simp [hf]