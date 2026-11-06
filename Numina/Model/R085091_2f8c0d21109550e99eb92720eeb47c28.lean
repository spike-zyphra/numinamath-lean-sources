import Mathlib

theorem number_theory_315782 :
    ∃ s : Finset ℕ, 22 ∈ s ∧ 2^100 + 2^97 - 2 ∈ s := by
  use {22, 2^100 + 2^97 - 2}
  constructor
  · -- Show that 22 ∈ s
    simp
  · -- Show that 2^100 + 2^97 - 2 ∈ s
    simp