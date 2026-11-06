import Mathlib

theorem algebra_13585 : {(x : ℂ) | x ^ 4 + 64 = 0} =
{2 + 2 * .I , -2 - 2 * .I , -2 + 2 * .I , 2 - 2 * .I} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First, assume x^4 + 64 = 0, and prove the four cases.
    intro h
    have h1 : x^4 + 64 = 0 := h
    have h3 : (x - (2 + 2 * Complex.I)) * (x - (2 - 2 * Complex.I)) * (x - (-2 + 2 * Complex.I)) * (x - (-2 - 2 * Complex.I)) = 0 := by
      have eq1 : (x - (2 + 2 * Complex.I)) * (x - (2 - 2 * Complex.I)) * (x - (-2 + 2 * Complex.I)) * (x - (-2 - 2 * Complex.I)) = x^4 + 64 := by 
        simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I, mul_add, mul_assoc, add_mul, mul_add, mul_assoc, mul_comm, mul_assoc]
        <;> ring_nf <;> norm_num
        <;> ring_nf <;> norm_num
      rw [eq1] at *
      rw [h1]
      <;> ring_nf <;> norm_num
    cases' (mul_eq_zero.mp h3) with h4 h5
    cases' mul_eq_zero.mp h4 with h6 h7
    cases' mul_eq_zero.mp h6 with h8 h9
    · -- Case x - (2 + 2 * i) = 0
      have hx : x = 2 + 2 * Complex.I := by
        exact eq_of_sub_eq_zero h8
      simp [hx]
      <;> norm_num [Complex.ext_iff]
    · -- Case x - (2 - 2 * i) = 0
      have hx : x = 2 - 2 * Complex.I := by
        exact eq_of_sub_eq_zero h9
      simp [hx]
      <;> norm_num [Complex.ext_iff]
    · -- Case x - (-2 + 2 * i) = 0
      have hx : x = -2 + 2 * Complex.I := by
        exact eq_of_sub_eq_zero h7
      simp [hx]
      <;> norm_num [Complex.ext_iff]
    · -- Case x - (-2 - 2 * i) = 0
      have hx : x = -2 - 2 * Complex.I := by
        exact eq_of_sub_eq_zero h5
      simp [hx]
      <;> norm_num [Complex.ext_iff]
  · -- Now the reverse direction. Show that each of the four elements satisfies x^4 + 64 = 0.
    rintro (rfl | rfl | rfl | rfl)
    · -- Check x = 2 + 2 * i
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num [Complex.ext_iff]
    · -- Check x = -2 - 2 * i
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num [Complex.ext_iff]
    · -- Check x = -2 + 2 * i
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num [Complex.ext_iff]
    · -- Check x = 2 - 2 * i
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num [Complex.ext_iff]