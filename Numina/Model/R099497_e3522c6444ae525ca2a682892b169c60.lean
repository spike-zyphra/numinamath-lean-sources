import Mathlib

theorem algebra_241841 (z : ℂ) (hz : z.re = 9) (hzz : (z^2).im = (z^3).im) :
    z = 9 ∨ z = 9 + 15 * .I ∨ z = 9 - 15 * .I := by
  have hzim : z.im ^ 3 - 225 * z.im = 0 := by
    simp [pow_two, pow_three, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, hz] at hzz ⊢
    nlinarith
  have h1 : z.im * (z.im ^ 2 - 225) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h1) with
  | inl h1 =>
    have hz0 : z.im = 0 := by linarith
    have h1 : z = 9 := by
      simp [Complex.ext_iff, hz, hz0]
    left
    exact h1
  | inr h2 =>
    have h3 : z.im ^ 2 = 225 := by linarith
    have h4 : z.im = 15 ∨ z.im = -15 := by
      have h5 : z.im ^ 2 - 225 = 0 := by linarith
      have h6 : z.im ^ 2 - 225 = (z.im - 15) * (z.im + 15) := by ring
      rw [h6] at h5
      cases (mul_eq_zero.mp h5) with
      | inl h7 =>
        left
        linarith
      | inr h8 =>
        right
        linarith
    cases h4 with
    | inl him15 =>
      have h2 : z = 9 + 15 * Complex.I := by
        simp [Complex.ext_iff, hz, him15]
        all_goals norm_num
      right
      left
      exact h2
    | inr him15 =>
      have h3 : z = 9 - 15 * Complex.I := by
        simp [Complex.ext_iff, hz, him15]
        all_goals norm_num
      right
      right
      exact h3