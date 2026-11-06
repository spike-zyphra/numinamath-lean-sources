import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_186854 (f g : ℝ → ℝ)
  (hf : f = λ x => x) (hg : g = λ x => 2 * x) :
  ∃ c d : ℝ, c ≠ 0 ∧ ∀ x ∈ Set.Icc 0 1, c * f x + d * g x = 0 := by
  use -2, 1
  constructor
  · norm_num
  · intro x hx
    rw [hf, hg]
    simp at hx ⊢
    <;> linarith