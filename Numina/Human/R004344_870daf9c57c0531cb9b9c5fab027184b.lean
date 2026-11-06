import Mathlib

open Complex

theorem algebra_255043 : ((-1 + I * √3) / 2)^1986 +
    ((-1 - I * √3) / 2)^1986 = 2 := by

  have h1 : ((-1 + I * √3) / 2) ^ 3 = 1 := by
    simp [pow_succ, pow_zero, Complex.ext_iff, mul_add, mul_sub, pow_two, add_mul, sub_mul, mul_comm, mul_assoc]
    ring_nf
    norm_num
    rw [show √3 ^ 3 = 3 * √3 by rw [pow_succ]; simp]
    ring

  have h2 : ((-1 - I * √3) / 2) ^ 3 = 1 := by
    simp [pow_succ, pow_zero, Complex.ext_iff, mul_add, mul_sub, pow_two, add_mul, sub_mul, mul_comm, mul_assoc]
    ring_nf
    norm_num
    rw [show √3 ^ 3 = 3 * √3 by rw [pow_succ]; simp]
    ring

  have h3 : ((-1 + I * √3) / 2) ^ 1986 = 1 := by
    calc ((-1 + I * √3) / 2) ^ 1986
      _ = (((-1 + I * √3) / 2) ^ 3) ^ 662 := by rw [← pow_mul]
      _ = 1 ^ 662 := by rw [h1]
      _ = 1 := by norm_num

  have h4 : ((-1 - I * √3) / 2) ^ 1986 = 1 := by
    calc ((-1 - I * √3) / 2) ^ 1986
      _ = (((-1 - I * √3) / 2) ^ 3) ^ 662 := by rw [← pow_mul]
      _ = 1 ^ 662 := by rw [h2]
      _ = 1 := by norm_num

  rw [h3, h4]
  norm_num
