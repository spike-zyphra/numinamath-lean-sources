import Mathlib

theorem number_theory_262163 (a b c d : ℤ) (ha : a = 10430) (hb : b = 3970)
    (hc : c = 2114) (hd : d = 386) :
    IsSquare (a + b) ∧ IsSquare (a + c) ∧ IsSquare (a + d) ∧ IsSquare (b + c) ∧
    IsSquare (b + d) ∧ IsSquare (c + d) ∧ IsSquare (a + b + c + d) := by
  rw [ha, hb, hc, hd]
  constructor
  · -- Show that 10430 + 3970 is a perfect square
    native_decide
  constructor
  · -- Show that 10430 + 2114 is a perfect square
    native_decide
  constructor
  · -- Show that 10430 + 386 is a perfect square
    native_decide
  constructor
  · -- Show that 3970 + 2114 is a perfect square
    native_decide
  constructor
  · -- Show that 3970 + 386 is a perfect square
    native_decide
  constructor
  · -- Show that 2114 + 386 is a perfect square
    native_decide
  · -- Show that 10430 + 3970 + 2114 + 386 is a perfect square
    native_decide