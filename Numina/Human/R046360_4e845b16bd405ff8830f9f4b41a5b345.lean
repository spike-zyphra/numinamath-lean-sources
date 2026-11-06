import Mathlib

open Real Set
open scoped BigOperators

/- Compute the range of the function $f(x) = \sqrt{x^2}$. -/
theorem algebra_18794 (f : ℝ → ℝ) (hf : f = λ x => sqrt (x ^ 2)) :
    range f = {y | 0 ≤ y} := by 
  rw [hf]
  ext y
  simp [hf, sq_sqrt]
  constructor
  intro h
  rcases h with ⟨x, rfl⟩
  apply sqrt_nonneg
  intro h
  use y
  simp [h]