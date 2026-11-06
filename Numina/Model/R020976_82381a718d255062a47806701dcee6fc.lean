import Mathlib

theorem algebra_248464 : ((1 + Complex.I)^1989 / ((1 - Complex.I)^1989 - (1 + Complex.I)^1989)) = (Complex.I - 1) / 2 := by
  have h1 : (1 + Complex.I) ^ 4 = -4 := by
    simp [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.I_mul_I]
    <;> norm_num
  have h2 : (1 - Complex.I) ^ 4 = -4 := by
    simp [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.I_mul_I]
    <;> norm_num
  have h5 : 1989 = 4 * 497 + 1 := by
    norm_num
  have h8 : (1 + Complex.I) ^ 1989 = (1 + Complex.I) * ((-4) ^ 497) := by
    rw [h5]
    rw [pow_add, pow_mul]
    rw [h1]
    all_goals ring_nf
  have h9 : (1 - Complex.I) ^ 1989 = (1 - Complex.I) * ((-4) ^ 497) := by
    rw [h5]
    rw [pow_add, pow_mul]
    rw [h2]
    all_goals ring_nf
  rw [h8, h9]
  field_simp [pow_mul, pow_two, Complex.ext_iff, Complex.I_mul_I, sub_eq_zero, mul_comm]
  <;> ring_nf <;> norm_num [Complex.I_mul_I, pow_two, Complex.ext_iff]
  <;> ring_nf <;> norm_num [Complex.I_mul_I, pow_two, Complex.ext_iff, pow_succ]
  <;> ring_nf <;> norm_num [Complex.I_mul_I, pow_two, Complex.ext_iff, pow_three]
  <;> ring_nf
  <;> norm_num [Complex.ext_iff, h1, h2]
  all_goals norm_num [Complex.ext_iff, h1, h2]
  <;> ring_nf
  <;> norm_num [Complex.ext_iff, h1, h2]
  <;> ring_nf
  <;> norm_num [Complex.ext_iff, h1, h2]
  all_goals norm_num [Complex.ext_iff, h1, h2]