import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_44353 {f : ℝ → ℝ} (hf : f = λ x => 3 * x ^ 2 / 4) :
    ∀ a > 0, ∃ x, (x ^ 2 - a ^ 2) ^ 2 = 4 * a ^ 2 * x ^ 2 := by
  intro a ha
  use 0
  have ha1 : (0 : ℕ) ^ 2 = (0 : ℕ) := by rfl
  all_goals
    simp at *