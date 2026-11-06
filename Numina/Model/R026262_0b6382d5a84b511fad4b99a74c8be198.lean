import Mathlib

theorem algebra_7631 : (Complex.I + 1) ^ 2 / (Complex.I - 1) ^ 2 = -1 := by
  have h1 : (Complex.I + 1 : ℂ) ^ 2 = 2 * Complex.I := by
    calc
      (Complex.I + 1 : ℂ) ^ 2 = (Complex.I) ^ 2 + 2 * Complex.I + 1 := by ring
      _ = -1 + 2 * Complex.I + 1 := by rw [Complex.I_sq]
      _ = 2 * Complex.I := by ring_nf
  have h2 : (Complex.I - 1 : ℂ) ^ 2 = -2 * Complex.I := by
    calc
      (Complex.I - 1 : ℂ) ^ 2 = (Complex.I) ^ 2 - 2 * Complex.I + 1 := by ring
      _ = -1 - 2 * Complex.I + 1 := by rw [Complex.I_sq]
      _ = -2 * Complex.I := by ring_nf
  rw [h1, h2]
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  <;> norm_num
  <;> ring_nf <;> norm_num