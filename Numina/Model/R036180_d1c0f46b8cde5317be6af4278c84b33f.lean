import Mathlib

open Complex

theorem algebra_22117 (ω : ℂ) (hω : ‖ω‖ = 1) (z : ℂ) (hz : z^2 + z + ω = 0) (hz1 : z.re = 0) :
  ω + starRingEnd ℂ ω = Real.sqrt 5 - 1 := by
  have h1 := hz
  simp [pow_two, hz1, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at h1 hz
  ring_nf at h1
  have eq1 := h1.1
  have eq2 := h1.2
  have h2 : ω.re = z.im ^ 2 := by
    nlinarith
  have h3 : ω.im = - z.im := by
    nlinarith
  have h3a : ω.re ^ 2 + ω.im ^ 2 = 1 := by
    have h_mod : ‖ω‖ = 1 := hω
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq] at h_mod ⊢
    ring_nf at h_mod ⊢
    nlinarith
  rw [show ω.re = z.im ^ 2 by nlinarith, show ω.im = -z.im by nlinarith] at h3a
  have h4 : z.im ^ 4 + z.im ^ 2 - 1 = 0 := by
    nlinarith
  have h5 : z.im ^ 2 = (-1 + Real.sqrt 5) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (z.im ^ 2 - (-1 + Real.sqrt 5) / 2)]
  have h7 : ω.re = (-1 + Real.sqrt 5) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, h7, show ω.im = -z.im by nlinarith]
  <;> ring_nf <;> norm_num
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]