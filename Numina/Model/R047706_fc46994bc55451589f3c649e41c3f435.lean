import Mathlib

theorem algebra_21389 {V I Z : ℂ} (hV : V = 1 + Complex.I) (hZ : Z = 2 - Complex.I)
    (hOhmsLaw : V = I * Z) : I = 1 / 5 + 3 / 5 * Complex.I := by
  rw [hV, hZ] at hOhmsLaw
  have eq1 := congr_arg Complex.re hOhmsLaw
  have eq2 := congr_arg Complex.im hOhmsLaw
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have eq3 : I.re = 1 / 5 := by
    linarith
  have eq4 : I.im = 3 / 5 := by
    linarith
  rw [Complex.ext_iff]
  simp [eq3, eq4]
  <;> all_goals linarith