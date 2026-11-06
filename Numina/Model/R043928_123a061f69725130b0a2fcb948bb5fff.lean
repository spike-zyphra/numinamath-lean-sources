import Mathlib

theorem algebra_15243 : {z : ℂ | z^4 = -4} = {1 + Complex.I, 1 - Complex.I, -1 + Complex.I, -1 - Complex.I} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- If z^4 = -4, then z is one of the four complex numbers.
    intro h
    have h1 : z^4 = -4 := h
    have h2 : z^4 + 4 = 0 := by
      calc
        z^4 + 4 = z^4 + (4 : ℂ) := by norm_num
        _ = -4 + 4 := by rw [h1]
        _ = 0 := by norm_num
    have h3 : z^4 + 4 = (z - (1 + Complex.I)) * (z - (1 - Complex.I)) * (z - (-1 + Complex.I)) * (z - (-1 - Complex.I)) := by 
      simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      <;> ring_nf <;> norm_num [Complex.I_sq]
    rw [h3] at h2
    cases' (mul_eq_zero.mp h2) with h4 h5
    cases' (mul_eq_zero.mp h4) with h6 h7
    cases' (mul_eq_zero.mp h6) with h8 h9
    · -- Case where z - (1 + i) = 0
      have h10 : z = 1 + Complex.I := by
        exact eq_of_sub_eq_zero h8
      simp [h10]
    · -- Case where z - (1 - i) = 0
      have h11 : z = 1 - Complex.I := by
        exact eq_of_sub_eq_zero h9
      simp [h11]
    · -- Case where z - (-1 + i) = 0
      have h12 : z = -1 + Complex.I := by
        exact eq_of_sub_eq_zero h7
      simp [h12]
    · -- Case where z - (-1 - i) = 0
      have h13 : z = -1 - Complex.I := by
        exact eq_of_sub_eq_zero h5
      simp [h13]
  · -- If z is one of the four complex numbers, then z^4 = -4.
    rintro (rfl | rfl | rfl | rfl)
    · -- z = 1 + i
      norm_num [pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    · -- z = 1 - i
      norm_num [pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    · -- z = -1 + i
      norm_num [pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    · -- z = -1 - i
      norm_num [pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]