import Mathlib

theorem algebra_16897 : ((-1 + Complex.I * Real.sqrt 3) / 2)^6 + ((-1 - Complex.I * Real.sqrt 3) / 2)^6 = 2 := by
  have h1 : ((-1 + Complex.I * Real.sqrt 3) / 2) ^ 3 = 1 := by
    simp [pow_three]
    field_simp [Complex.ext_iff, mul_add, add_mul, pow_two, mul_comm, mul_assoc]
    <;> ring_nf <;> norm_num [Real.sqrt_sq] <;> ring
    <;> norm_num [mul_add, add_mul, pow_two, Real.sqrt_sq] <;> ring
  have h2 : ((-1 - Complex.I * Real.sqrt 3) / 2) ^ 3 = 1 := by
    simp [pow_three]
    field_simp [Complex.ext_iff, mul_add, add_mul, pow_two, mul_comm, mul_assoc]
    <;> ring_nf <;> norm_num [Real.sqrt_sq] <;> ring
    <;> norm_num [mul_add, add_mul, pow_two, Real.sqrt_sq] <;> ring
  have h3 : ((-1 + Complex.I * Real.sqrt 3) / 2) ^ 6 = 1 := by
    calc
      ((-1 + Complex.I * Real.sqrt 3) / 2) ^ 6
        = (((-1 + Complex.I * Real.sqrt 3) / 2) ^ 3) ^ 2 := by ring_nf
      _ = 1 ^ 2 := by rw [h1]
      _ = 1 := by ring_nf
  have h4 : ((-1 - Complex.I * Real.sqrt 3) / 2) ^ 6 = 1 := by
    calc
      ((-1 - Complex.I * Real.sqrt 3) / 2) ^ 6
        = (((-1 - Complex.I * Real.sqrt 3) / 2) ^ 3) ^ 2 := by ring_nf
      _ = 1 ^ 2 := by rw [h2]
      _ = 1 := by ring_nf
  rw [h3, h4]
  all_goals ring_nf <;> norm_num