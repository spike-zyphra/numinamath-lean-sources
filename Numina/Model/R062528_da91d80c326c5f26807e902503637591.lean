import Mathlib

theorem number_theory_12226 (M : Finset ℕ) (hM : M = Finset.Icc 1 2017) :
    ∃ x ∈ M, IsSquare (∑ y ∈ M \ {x}, y) ↔ x = 1677 := by
  rw [hM]
  use 1677
  simp
  <;> native_decide