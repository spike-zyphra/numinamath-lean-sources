import Mathlib

theorem algebra_21557 : (2 + 3 * Complex.I) * (1 - 2 * Complex.I) = 8 - Complex.I := by 
  calc
    (2 + 3 * Complex.I) * (1 - 2 * Complex.I)
        = 2 * 1 + 2 * (-2 * Complex.I) + 3 * Complex.I * 1 + 3 * Complex.I * (-2 * Complex.I) := by ring
    _ = 2 - 4 * Complex.I + 3 * Complex.I - 6 * (Complex.I * Complex.I) := by ring
    _ = 2 - 4 * Complex.I + 3 * Complex.I - 6 * (-1) := by 
      rw [Complex.I_mul_I]
    _ = 2 - 4 * Complex.I + 3 * Complex.I + 6 := by ring
    _ = 8 - Complex.I := by 
      ring