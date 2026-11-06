import Mathlib

theorem number_theory_2353 : IsLeast {x : ℕ | 0 < x} 1 := by
  constructor
  · -- Show that 1 is in the set
    simp
  · -- Show that for all x in the set, 1 ≤ x
    intro x hx
    simp at hx ⊢
    omega