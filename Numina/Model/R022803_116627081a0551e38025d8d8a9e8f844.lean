import Mathlib

theorem algebra_323930 {z : ℂ} (hz : z + Complex.abs z = 2 + Complex.I) :
    z = 3 / 4 + Complex.I := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2
  have hy : z.im = 1 := by linarith
  have hz_re : z.re + Complex.abs z = 2 := by
    linarith
  have h_abs : Complex.abs z = Real.sqrt ((z.re)^2 + (z.im)^2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  rw [h_abs, hy] at hz_re
  have eq3 : z.re + Real.sqrt ((z.re)^2 + 1) = 2 := by
    norm_num at hz_re ⊢
    linarith
  have h1 : Real.sqrt ((z.re)^2 + 1) = 2 - z.re := by
    linarith
  have h2 : (z.re)^2 + 1 = (2 - z.re)^2 := by
    calc
      (z.re)^2 + 1 = (Real.sqrt ((z.re)^2 + 1))^2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (2 - z.re)^2 := by
        rw [h1]
  have h3 : (z.re)^2 + 1 = 4 - 4 * z.re + (z.re)^2 := by
    nlinarith [h2]
  have h4 : z.re = 3 / 4 := by
    linarith
  have h5 : z = 3 / 4 + Complex.I := by
    simp [Complex.ext_iff, h4, hy]
  exact h5