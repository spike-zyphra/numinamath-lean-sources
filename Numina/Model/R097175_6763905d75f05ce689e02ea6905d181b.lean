import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_168568 {f : ℝ → ℝ} (hf : f = λ x => sqrt (4 - x^2) / log (abs x + x)) :
    ∀ x, x ∈ Ioo 0 (1/2) ∪ Ioc (1/2) 2 → f x = sqrt (4 - x^2) / log (abs x + x) := by 
  intros x h1
  rcases h1 with (h1 | h1)
  · -- first case where x ∈ (0, 1/2)
    rw [hf]
  · -- second case where x ∈ (1/2, 2]
    rw [hf]