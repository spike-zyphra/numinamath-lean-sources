import Mathlib

theorem algebra_14220 : ((1 + Complex.I) / (1 - Complex.I)) ^ 1000 = 1 := by
  have h1 : (1 + Complex.I) / (1 - Complex.I) = Complex.I := by
    field_simp [Complex.ext_iff, Complex.I_mul_I]
    <;> try norm_num
  rw [h1]
  have h2 : Complex.I ^ 4 = 1 := by
    calc
      Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by simp [Complex.I_sq]
      _ = 1 := by norm_num
  calc
    Complex.I ^ 1000 = Complex.I ^ (4 * 250) := by norm_num
    _ = (Complex.I ^ 4) ^ 250 := by rw [pow_mul]
    _ = (1) ^ 250 := by rw [h2]
    _ = 1 := by norm_num