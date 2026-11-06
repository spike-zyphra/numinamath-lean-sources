import Mathlib

theorem algebra_158211 {G : Type*} [AddCommGroup G] [Fintype G] :
    ∀ x : G, Fintype.card G • x = 0 := by
  intro x
  simp [Finset.sum_eq_zero]