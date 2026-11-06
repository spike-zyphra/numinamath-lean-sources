import Mathlib

theorem algebra_306605 {A : Type*} [Fintype A] (f : A → A)
    (h₀ : Function.Injective f) :
    ∃ m, ∀ x, f^[m] x = x := by 
  use 0
  intro x
  simp