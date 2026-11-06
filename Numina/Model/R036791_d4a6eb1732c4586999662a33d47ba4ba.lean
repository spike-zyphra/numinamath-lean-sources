import Mathlib

theorem algebra_16599 :
    {z : ℂ | z ^ 2 - z = 5 - 5 * .I} = {3 - .I, -2 + .I} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward: z^2 - z = 5 - 5i → z ∈ {3 - i, -2 + i}
    intro h
    have eq1 := congr_arg Complex.re h
    have eq2 := congr_arg Complex.im h
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, sub_eq_zero] at eq1 eq2
    have eq3 : (z.re - 3) * (z.re + 2) = 0 := by
      nlinarith [sq_nonneg (z.re - 3), sq_nonneg (z.re + 2), sq_nonneg (z.im + 1), sq_nonneg (z.im - 1), sq_nonneg (z.re * z.im)]
    have eq4 : z.re - 3 = 0 ∨ z.re + 2 = 0 := by
      cases (mul_eq_zero.mp eq3) with
      | inl h3 =>
        left
        linarith
      | inr h4 =>
        right
        linarith
    cases eq4 with
    | inl h5 =>
      have eq5 : z.re = 3 := by linarith
      have eq6 : z.im = -1 := by
        rw [eq5] at eq2
        nlinarith
      left
      simp [Complex.ext_iff, eq5, eq6]
    | inr h6 =>
      have eq7 : z.re = -2 := by linarith
      have eq8 : z.im = 1 := by
        rw [eq7] at eq2
        nlinarith
      right
      simp [Complex.ext_iff, eq7, eq8]
  · -- Backward: z ∈ {3 - i, -2 + i} → z^2 - z = 5 - 5i
    rintro (rfl | rfl)
    · -- Check z = 3 - i
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num
    · -- Check z = -2 + i
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num