import Mathlib

theorem algebra_28669 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ∃ x : ℚ, x ^ 2 + (a + b) ^ 2 * x + 4 * a * b = 1 ↔ a = b := by
  use -1
  constructor
  · -- Assume the equation holds at x = -1, prove a = b
    intro h
    have h_eq2 : (a : ℚ) = (b : ℚ) := by
      have h_eq : (-1 : ℚ) ^ 2 + (a + b : ℚ) ^ 2 * (-1 : ℚ) + 4 * (a : ℚ) * (b : ℚ) = 1 := by
        simpa using h
      nlinarith [sq_nonneg ((a : ℚ) - (b : ℚ)), sq_nonneg ((a : ℚ) + (b : ℚ)), show (a : ℚ) > 0 by exact_mod_cast ha, show (b : ℚ) > 0 by exact_mod_cast hb]
    have h_eq : a = b := by
      exact_mod_cast h_eq2
    exact_mod_cast h_eq
  · -- Assume a = b, prove the equation holds at x = -1
    intro h_eq
    have h_eq2 : (a : ℚ) = (b : ℚ) := by exact_mod_cast h_eq
    have h_eq3 : (-1 : ℚ) ^ 2 + (a + b : ℚ) ^ 2 * (-1 : ℚ) + 4 * (a : ℚ) * (b : ℚ) = 1 := by
      rw [show (b : ℚ) = (a : ℚ) by linarith [h_eq2]]
      ring
    simpa using h_eq3