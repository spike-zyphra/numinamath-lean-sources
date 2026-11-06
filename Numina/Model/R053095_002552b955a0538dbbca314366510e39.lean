import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_148434 (f : ℝ → ℝ) (hf : f = λ x => 3 / (2 - cos x)) :
    ∀ x, f x ∈ univ := by
  intro x
  simp [hf]
  all_goals norm_num [Real.cos_sq_add_sin_sq]
  <;> try { simp }
  all_goals norm_num [Real.cos_sq_add_sin_sq]