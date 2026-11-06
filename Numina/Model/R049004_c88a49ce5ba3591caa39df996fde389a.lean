import Mathlib

theorem number_theory_261324 (a : Fin 6 → ℕ) (ha : a 0 = 4784887 ∧ a 1 = 2494651 ∧ a 2 = 8595087 ∧ a 3 = 1385287 ∧ a 4 = 9042451 ∧ a 5 = 9406087) :
    ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ IsSquare (a x + a y + a z) := by 
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩
  use 1, 3, 5
  constructor
  · -- Show that 1 ≠ 3
    simp
  constructor
  · -- Show that 3 ≠ 5 
    simp
  constructor
  · -- Show that 5 ≠ 1 
    simp 
  · -- Now we need to prove that the sum is a square. 
    rw [ha1, ha3, ha5]
    native_decide