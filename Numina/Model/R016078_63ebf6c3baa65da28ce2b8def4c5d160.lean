import Mathlib

theorem number_theory_161502 : ∃ (a : Fin 2016 → ℤ), (∏ i, a i = 9) ∧ (∑ i, a i = 0) := by
  use fun i => if i.val < 2 then 3 else if i.val < 1006 then 1 else -1
  constructor
  · -- Show that the product is 9
    native_decide
  · -- Show that the sum is 0
    native_decide