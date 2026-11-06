import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_126624 {α : ℝ} (hα : α > 0) (a b : ℝ → ℕ)
  (ha : ∀ t, a t = ⌊t / 1⌋) (hb : ∀ t, b t = ⌊(t - α) / 1⌋)
  (S : Set ℝ) (hS : S = {t | α ≤ t ∧ a t = 2 * b t}) :
  ∃ n, ∃ c : Fin n → ℝ,
    (∀ i, α ≤ c i) ∧
    (∀ i, c i < α + 1) ∧
    (∑ i, (α + 1 - c i)) = 1 := by
  use 1
  use fun i => α
  constructor
  · -- Show that ∀ i, α ≤ α
    intro i
    simp
  constructor
  · -- Show that ∀ i, α < α + 1
    intro i
    simp
    all_goals linarith
  · -- Show that ∑ i, (α + 1 - c i) = 1
    simp
    all_goals linarith