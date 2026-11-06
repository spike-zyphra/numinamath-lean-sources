import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem other_55087 {X : Type*} [TopologicalSpace X] [T2Space X]
  (G : ℕ → Set X) (hG : ∀ n, IsOpen (G n)) :
  ∃ V : ℕ → Set X, (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
  (∀ i, IsOpen (V i)) ∧ (∃ n : ℕ → ℕ, (∀ i, n i < n (i + 1)) ∧
  (∀ i, V i ⊆ G (n i))) := by

  use fun i => (∅ : Set X)
  constructor
  · -- Show that all sets are pairwise disjoint
    intro i j h
    simp
  constructor
  · -- Show that all sets are open
    intro i
    simp
    all_goals try tauto
  · -- Let n be any strictly increasing function
    use (fun i => i + 1)
    constructor
    · -- Show that n is strictly increasing
      intro i
      simp
      all_goals omega
    · -- Show that each set is contained in G(n i)
      intro i
      simp