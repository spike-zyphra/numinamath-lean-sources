import Mathlib

theorem algebra_611431 :
    {z : ℂ | z ^ 4 + 4 * z ^ 2 + 6 = z} = {(1 - Complex.I * Real.sqrt 7) / 2, (1 + Complex.I * Real.sqrt 7) / 2, (-1 - Complex.I * Real.sqrt 11) / 2, (-1 + Complex.I * Real.sqrt 11) / 2} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, show that if $z$ is a solution, then it must be one of the four complex numbers.
    intro h_eq
    have h_eq1 : z^4 +4 * z^2 - z +6 =0 := by
      calc
        z^4 +4 * z^2 - z +6 = (z^4 +4 * z^2 +6) - z := by ring
        _ = z - z := by rw [h_eq]
        _ = 0 := by simp
    have h2 : z^4 + 4 * z^2 - z +6 = (z - ((1 - Complex.I * Real.sqrt 7) / 2)) * (z - ((1 + Complex.I * Real.sqrt 7) / 2)) * (z - ((-1 - Complex.I * Real.sqrt 11) / 2)) * (z - ((-1 + Complex.I * Real.sqrt 11) / 2)) := by
      simp [pow_two, pow_succ, Complex.ext_iff, mul_add, sub_eq_zero, mul_comm, mul_assoc]
      ring_nf
      <;> simp [Complex.I_sq, mul_add, add_mul, pow_two, mul_comm, mul_assoc, mul_left_comm]
      <;> ring_nf
      <;> norm_num [Real.sqrt_sq]
    rw [h2] at h_eq1
    cases' (mul_eq_zero.mp h_eq1) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case $z - ( (1 - i\sqrt{7})/2 ) = 0$
      have h_eq2 : z = (1 - Complex.I * Real.sqrt 7) / 2 := by
        exact eq_of_sub_eq_zero h7
      rw [h_eq2]
      left
      simp
    · -- Case $z - ( (1 + i\sqrt{7})/2 ) = 0$
      have h_eq2 : z = (1 + Complex.I * Real.sqrt 7) / 2 := by
        exact eq_of_sub_eq_zero h8
      rw [h_eq2]
      right
      left
      simp
    · -- Case $z - ( ( -1 - i\sqrt{11})/2 ) = 0$
      have h_eq2 : z = (-1 - Complex.I * Real.sqrt 11) / 2 := by
        exact eq_of_sub_eq_zero h6
      rw [h_eq2]
      right
      right
      left
      simp
    · -- Case $z - ( ( -1 + i\sqrt{11})/2 ) = 0$
      have h_eq2 : z = (-1 + Complex.I * Real.sqrt 11) / 2 := by
        exact eq_of_sub_eq_zero h4
      rw [h_eq2]
      right
      right
      right
      simp
  · -- Now, show the reverse. Each of the four complex numbers is a solution.
    rintro (h | h | h | h)
    · -- Case $z = (1 - i\sqrt{7})/2$
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, mul_add, add_mul, pow_two, mul_comm, mul_assoc]
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_sq, pow_two, mul_add, add_mul]
    · -- Case $z = (1 + i\sqrt{7})/2$
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, mul_add, add_mul, pow_two, mul_comm, mul_assoc]
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_sq, pow_two, mul_add, add_mul]
    · -- Case $z = (-1 - i\sqrt{11})/2$
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, mul_add, add_mul, pow_two, mul_comm, mul_assoc]
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_sq, pow_two, mul_add, add_mul]
    · -- Case $z = (-1 + i\sqrt{11})/2$
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, mul_add, add_mul, pow_two, mul_comm, mul_assoc]
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_sq, pow_two, mul_add, add_mul]