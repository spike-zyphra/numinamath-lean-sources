import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_17269 (f : ℝ → ℝ) (hf : f = λ x => sin (3 * x - π)) :
    f = λ x => sin (3 * (x - π / 3)) := by 
  funext x
  rw [hf]
  have h : 3 * (x - π / 3) = 3 * x - π := by
    ring_nf
  simp [h]
  all_goals ring_nf <;> norm_num