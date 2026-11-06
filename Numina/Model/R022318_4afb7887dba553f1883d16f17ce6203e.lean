import Mathlib

theorem algebra_311653 {a b : ℂ} (ha : a + 2 * (b.1 - Complex.I * b.2) = Complex.I)
    (hb : (a.1 - Complex.I * a.2) * (b.1 - Complex.I * b.2) = -5 - Complex.I) :
    Complex.abs a ^ 2 = 8 ∨ Complex.abs a ^ 2 = 13 := by
  have eq1 := congr_arg Complex.re ha
  have eq2 := congr_arg Complex.im ha
  have eq3 := congr_arg Complex.re hb
  have eq4 := congr_arg Complex.im hb
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at eq1 eq2 eq3 eq4

  have h1 : a.1 + 2 * b.1 = 0 := by linarith
  have h2 : a.2 - 2 * b.2 = 1 := by linarith
  have h3 : a.1 * b.1 - a.2 * b.2 = -5 := by linarith
  have h4 : a.1 * (-b.2) + (b.1) * (-a.2) = -1 := by linarith

  have eq5 : a.1 = -2 * b.1 := by linarith
  have eq6 : a.2 = 1 + 2 * b.2 := by linarith

  have h5 : -2 * (b.1)^2 - (b.2) - 2 * (b.2)^2 = -5 := by
    rw [show a.1 = -2 * b.1 by linarith [eq5], show a.2 = 1 + 2 * b.2 by linarith [eq6]] at h3
    nlinarith

  have h6 : a.1 * (-b.2) + (- (1 + 2 * b.2)) * b.1 = -1 := by
    rw [show a.1 = -2 * b.1 by linarith [eq5], show a.2 = 1 + 2 * b.2 by linarith [eq6]] at h4
    nlinarith

  have eq7 : b.1 = 1 := by
    nlinarith [h6]

  have eq8 : a.1 = -2 := by
    rw [eq7] at eq5 
    linarith

  have eq9 : 2 * (b.2)^2 + b.2 - 3 = 0 := by 
    rw [eq7] at h5 
    nlinarith

  have eq10 : (b.2 - 1) * (2 * b.2 + 3) = 0 := by 
    nlinarith

  cases (mul_eq_zero.1 eq10) with
  | inl h11 =>
    have eq11 : b.2 = 1 := by linarith
    have eq12 : a.2 = 3 := by
      rw [eq11] at eq6
      linarith
    have eq5 : Complex.abs a ^ 2 = 13 := by
      simp [Complex.abs, Complex.normSq]
      rw [eq8, eq12]
      all_goals norm_num
    right 
    linarith
  | inr h12 =>
    have eq13 : b.2 = -3 / 2 := by linarith
    have eq14 : a.2 = -2 := by
      rw [eq13] at eq6
      linarith
    have eq5 : Complex.abs a ^ 2 = 8 := by
      simp [Complex.abs, Complex.normSq]
      rw [eq8, eq14]
      all_goals norm_num
    left
    linarith