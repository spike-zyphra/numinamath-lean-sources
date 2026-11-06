import Mathlib

theorem number_theory_3292 (n : ℤ) (h : n > 2) :
  ∃ (a b c : ℤ), a^2 + b^2 = c^2 ∧ n ∈ ({a, b, c} : Finset ℤ) := by 
  use n, 0, n
  constructor
  · -- Show that n^2 + 0^2 = n^2
    ring
  · -- Show that n ∈ {n, 0, n}
    simp