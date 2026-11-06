import Mathlib

theorem algebra_328474 (n : ℕ) (hn : n > 0) :
    ((1 / 2) + (Real.sqrt 3 / 2) * Complex.I) ^ (6 * n) = 1 := by
  have h2 : ((1 / 2) + (Real.sqrt 3 / 2) * Complex.I) ^ 6 = 1 := by
    have h3 : ((1 / 2) + (Real.sqrt 3 / 2) * Complex.I) ^ 3 = -1 := by
      simp [pow_three]
      field_simp [Complex.ext_iff, mul_add, add_mul, pow_two, mul_comm, mul_assoc, Complex.I_mul_I]
      <;> ring_nf <;> simp [Real.sqrt_sq, mul_add, pow_two]
      <;> ring
    calc
      ((1 / 2) + (Real.sqrt 3 / 2) * Complex.I) ^ 6
          = (((1 / 2) + (Real.sqrt 3 / 2) * Complex.I) ^ 3) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [h3]
      _ = 1 := by norm_num

  calc
    ((1 / 2) + (Real.sqrt 3 / 2) * Complex.I) ^ (6 * n)
        = (((1 / 2) + (Real.sqrt 3 / 2) * Complex.I) ^ 6) ^ n := by
          rw [mul_comm]
          rw [pow_mul]
    _ = (1) ^ n := by
      rw [h2]
    _ = 1 := by
      simp