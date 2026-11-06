import Mathlib
theorem algebra_9341 : (Complex.I * (3 - 4 * Complex.I)).re = 4 ∧ (Complex.I * (3 - 4 * Complex.I)).im = 3 := by
  have h1 : Complex.I * (3 - 4 * Complex.I) = 4 + 3 * Complex.I := by
    calc
      Complex.I * (3 - 4 * Complex.I)
          = 3 * Complex.I - 4 * Complex.I^2 := by ring
      _ = 3 * Complex.I - 4 * (-1) := by rw [Complex.I_sq]
      _ = 3 * Complex.I + 4 := by ring
      _ = 4 + 3 * Complex.I := by ring
  rw [h1]
  constructor
  · -- Real part is 4
    simp
  · -- Imaginary part is 3
    simp