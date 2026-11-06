import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_178862 {f : ℝ → ℝ} (hf : f = λ x => 4 / x) :
    ∃ K R X Y, K = sqrt 2 / 4 ∧ R = 2 * sqrt 2 ∧ X = 4 ∧ Y = 4 := by 
  exact ⟨sqrt 2 / 4, 2 * sqrt 2, 4, 4, rfl, rfl, rfl, rfl⟩