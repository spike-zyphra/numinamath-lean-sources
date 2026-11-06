import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_143970 {f : ℝ → ℝ} (hf : f = λ x => (x - 2)^2 / (2 * x + 2)) :
    ∀ x, f x = (x - 2)^2 / (2 * x + 2) := by 
  intro x 
  simp [hf]