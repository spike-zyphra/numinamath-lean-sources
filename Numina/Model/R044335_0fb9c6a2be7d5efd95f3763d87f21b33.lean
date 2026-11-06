import Mathlib

open Set Real
open scoped BigOperators

theorem other_280976 {A : Type*} [Infinite A] :
  ∃ (s : Set A), Countable s ∧ s ≠ ⊤ := by
  use ∅
  constructor
  · -- Show that the empty set is countable
    simp
  · -- Show that the empty set is not equal to the top set
    simp [Set.ext_iff]
    all_goals tauto