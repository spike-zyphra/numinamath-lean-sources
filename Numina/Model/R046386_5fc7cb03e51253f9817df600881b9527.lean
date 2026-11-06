import Mathlib

theorem number_theory_6451 (f : ZMod 7 → ZMod 7) (hf : f = fun x => 2*x^3 + 5*x^2 + 6*x + 1) :
    ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ f x = 0 ∧ f y = 0 ∧ f z = 0 := by
  use 1, 2, 5
  constructor
  · -- Show x ≠ y
    native_decide
  constructor
  · -- Show y ≠ z
    native_decide
  constructor
  · -- Show z ≠ x
    native_decide
  constructor
  · -- Show f 1 = 0
    rw [hf]
    simp
    <;> native_decide
  constructor
  · -- Show f 2 = 0
    rw [hf]
    simp
    <;> native_decide
  · -- Show f 5 = 0
    rw [hf]
    simp
    <;> native_decide