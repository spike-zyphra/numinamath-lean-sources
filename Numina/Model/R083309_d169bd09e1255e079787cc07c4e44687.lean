import Mathlib

theorem number_theory_2447 {x y : ℕ} (hx : x = 2^12 * 3^6) (hy : y = 2^8 * 3^8) :
    ∃ z, x^x * y^y = z^z ∧ z = 2^11 * 3^7 := by
  use 2 ^ 11 * 3 ^ 7
  constructor
  · -- Show x^x * y^y = z^z
    rw [hx, hy]
    native_decide
  · -- Show z = 2^11 * 3^7
    rfl