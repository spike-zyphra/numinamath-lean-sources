import Mathlib

theorem algebra_20388 :
    {a : ℝ | ∃ x : ℝ, (3 - Complex.I) * x ^ 2 + (a + 4 * Complex.I) * x - 115 + 5 * Complex.I = 0}
    = {8, -112} := by

  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]

  constructor
  · -- First, prove the forward direction: if there exists a real root x, then a ∈ {8, -112}.
    rintro ⟨x, h⟩
    have eq1 := congr_arg Complex.re h
    have eq2 := congr_arg Complex.im h

    simp [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2

    have h1 : x ^ 2 - 4 * x - 5 = 0 := by nlinarith

    have h2 : (x - 5) * (x + 1) = 0 := by
      nlinarith

    cases (mul_eq_zero.1 h2) with
    | inl h3 =>
      have hx : x = 5 := by linarith
      rw [hx] at eq1
      left
      linarith

    | inr h4 =>
      have hx : x = -1 := by linarith
      rw [hx] at eq1
      right
      linarith

  · -- Now the reverse direction: if a ∈ {8, -112}, then there exists a real root.
    rintro (h | h)
    · -- Case a = 8
      rw [h]
      use 5
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im]
      all_goals norm_num

    · -- Case a = -112
      rw [h]
      use -1
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im]
      all_goals norm_num