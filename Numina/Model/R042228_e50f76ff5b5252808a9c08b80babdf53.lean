import Mathlib

theorem algebra_10989 {V I Z : ℂ} (h : V = I * Z) (hV : V = 1 - .I) (hZ : Z = 1 + 3 * .I) :
    I = (-1 / 5) + (-2 / 5) * .I := by
  rw [hV] at h
  rw [hZ] at h
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, 
        Complex.add_im, Complex.mul_im, Complex.ofReal_im] at eq1 eq2 
  have eq3 : I.re = -1 / 5 := by
    nlinarith
  have eq4 : I.im = -2 / 5 := by 
    nlinarith [eq3]
  simp [Complex.ext_iff, eq3, eq4]
  <;> nlinarith