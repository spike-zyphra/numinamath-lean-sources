import Mathlib

theorem algebra_14362 : ((1 + Complex.I) / Real.sqrt 2) ^ 46 = -Complex.I := by
  have h1 : ((1 + Complex.I) / Real.sqrt 2) ^ 2 = Complex.I := by
    simp [pow_two, Complex.ext_iff, Complex.I_mul_I, mul_add, add_mul, pow_two, div_eq_mul_inv]
    field_simp [Real.sqrt_sq, Complex.ext_iff]
    <;> ring_nf <;> simp [Real.sqrt_sq]
  have h2 : ((1 + Complex.I) / Real.sqrt 2) ^ 4 = -1 := by
    calc
      ((1 + Complex.I) / Real.sqrt 2) ^ 4
        = (((1 + Complex.I) / Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = (Complex.I) ^ 2 := by rw [h1]
      _ = -1 := by simp [Complex.I_sq]
  have h4 : ((1 + Complex.I) / Real.sqrt 2) ^ 8 = 1 := by
    calc
      ((1 + Complex.I) / Real.sqrt 2) ^ 8
        = (((1 + Complex.I) / Real.sqrt 2) ^ 4) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [h2]
      _ = 1 := by norm_num
  have h5 : ((1 + Complex.I) / Real.sqrt 2) ^ 46 = ((1 + Complex.I) / Real.sqrt 2) ^ 6 := by
    calc
      ((1 + Complex.I) / Real.sqrt 2) ^ 46
        = ((1 + Complex.I) / Real.sqrt 2) ^ (8 * 5 + 6) := by norm_num
      _ = (((1 + Complex.I) / Real.sqrt 2) ^ 8) ^ 5 * ((1 + Complex.I) / Real.sqrt 2) ^ 6 := by
        rw [pow_add, pow_mul]
      _ = (1) ^ 5 * ((1 + Complex.I) / Real.sqrt 2) ^ 6 := by
        rw [h4]
      _ = ((1 + Complex.I) / Real.sqrt 2) ^ 6 := by ring
  have h6 : ((1 + Complex.I) / Real.sqrt 2) ^ 6 = -Complex.I := by
    calc
      ((1 + Complex.I) / Real.sqrt 2) ^ 6
        = ((1 + Complex.I) / Real.sqrt 2) ^ 4 * ((1 + Complex.I) / Real.sqrt 2) ^ 2 := by ring
      _ = (-1) * (Complex.I) := by
        rw [h2, h1]
      _ = -Complex.I := by ring
  rw [h5, h6]