import Mathlib

theorem number_theory_3637 :
    ∃ S : Finset ℕ, S.card > 0 ∧ (∀ p ∈ S, Nat.Prime p) ∧ Odd S.card ∧ Even (∑ p ∈ S, p) := by
  use {2}
  constructor
  · -- Show that {2} is non-empty, its cardinality equals 1 which is > 0
    simp
  constructor
  · -- Show that ∀ p ∈ {2}, Nat.Prime p
    intro p hp
    simp at hp
    rcases hp with (rfl)
    norm_num
  constructor
  · -- Show that {2} has odd cardinality
    decide
  · -- Show that ∑ p in {2}, p is even
    decide