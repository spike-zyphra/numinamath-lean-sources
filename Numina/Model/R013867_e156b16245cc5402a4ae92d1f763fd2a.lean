import Mathlib

open Real

theorem calculus_23050 : (-1 + Complex.I * sqrt 3)^8 = -128 - 128 * sqrt 3 * Complex.I := by 
  have h1 : (-1 + Complex.I * sqrt 3) ^ 2 = -2 - 2 * sqrt 3 * Complex.I := by
    simp [pow_two, Complex.ext_iff, mul_add, mul_comm, mul_assoc]
    ring_nf
    <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
    <;> ring_nf
    <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
    <;> tauto
  
  have h2 : (-1 + Complex.I * sqrt 3) ^ 4 = -8 + 8 * sqrt 3 * Complex.I := by
    calc
      (-1 + Complex.I * sqrt 3) ^ 4 = ((-1 + Complex.I * sqrt 3) ^ 2) ^ 2 := by ring
      _ = (-2 - 2 * sqrt 3 * Complex.I) ^ 2 := by rw [h1]
      _ = -8 + 8 * sqrt 3 * Complex.I := by
        simp [pow_two, Complex.ext_iff, mul_add, mul_comm, mul_assoc]
        ring_nf
        <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
        <;> ring_nf
        <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
        <;> tauto
  
  have h3 : (-1 + Complex.I * sqrt 3) ^ 8 = (-128 - 128 * sqrt 3 * Complex.I) := by
    calc
      (-1 + Complex.I * sqrt 3) ^ 8 = ((-1 + Complex.I * sqrt 3) ^ 4) ^ 2 := by ring
      _ = (-8 + 8 * sqrt 3 * Complex.I) ^ 2 := by rw [h2]
      _ = (-128 - 128 * sqrt 3 * Complex.I) := by
        simp [pow_two, Complex.ext_iff, mul_add, mul_comm, mul_assoc]
        ring_nf
        <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
        <;> ring_nf
        <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
        <;> tauto
  
  exact h3
  <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
  <;> ring_nf
  <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
  <;> tauto