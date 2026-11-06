import Mathlib

theorem algebra_97647 (k : ℝ) (hk : k < 0) (z : ℂ) (hz : 10 * z ^ 2 - 3 * Complex.I * z - k = 0) :
    ∃ w : ℂ, w ≠ z ∧ 10 * w ^ 2 - 3 * Complex.I * w - k = 0 ∧
    (z.re = 0 ∧ z.im ≠ 0) ∧ (w.re = 0 ∧ w.im ≠ 0) := by
  have eqn1 := congr_arg Complex.re hz
  have eqn2 := congr_arg Complex.im hz
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eqn1 eqn2
  ring_nf at eqn1 eqn2
  have h1 : z.re = 0 := by
    nlinarith [sq_nonneg (z.re), sq_pos_of_neg (show k < 0 by linarith), sq_nonneg (z.im)]
  use (3 * Complex.I / 10 - z)
  constructor
  · -- Show that w ≠ z
    by_contra h
    have hw1 : z.im = 0 := by
      have h_eq : 3 * Complex.I / 10 - z = z := by
        simpa using h
      have eq1 := congr_arg Complex.re h_eq
      have eq2 := congr_arg Complex.im h_eq
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h1] at eq1 eq2
      nlinarith [show k < 0 by linarith]
    rw [h1, hw1] at eqn1 eqn2
    nlinarith [sq_pos_of_neg (show k < 0 by linarith)]
  constructor
  · -- Show that 10w^2 - 3iw - k = 0
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, h1]
    <;> nlinarith [sq_nonneg (z.im), sq_pos_of_neg (show k < 0 by linarith)]
  constructor
  · -- Show that z.re = 0 and z.im ≠ 0
    constructor
    · exact h1
    · -- Show that z.im ≠ 0
      by_contra h
      rw [h1, h] at eqn1 eqn2
      nlinarith [sq_pos_of_neg (show k < 0 by linarith)]
  · -- Show that w.re = 0 and w.im ≠ 0
    constructor
    · -- Show that w.re = 0
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, h1]
      all_goals nlinarith
    · -- Show that w.im ≠ 0
      by_contra h
      have hw1 : z.im = 0 := by
        simp [Complex.I_im, Complex.sub_im, Complex.mul_im, h1] at h ⊢
        nlinarith [show k < 0 by linarith]
      rw [h1, hw1] at eqn1 eqn2
      nlinarith [sq_pos_of_neg (show k < 0 by linarith)]