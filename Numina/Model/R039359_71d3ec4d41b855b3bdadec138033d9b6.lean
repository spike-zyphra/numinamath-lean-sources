import Mathlib

theorem algebra_320078 {z : ℂ} (hz : z ^ 2 = 8 * .I) :
    z = 2 + 2 * .I ∨ z = -2 - 2 * .I := by 
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2 
  have eq3 : z.re ^ 2 - z.im ^ 2 = 0 := by linarith
  have eq4 : 2 * z.re * z.im = 8 := by linarith 
  have eq5 : z.re ^ 2 = z.im ^ 2 := by linarith 
  have eq6 : z.re = z.im ∨ z.re = -z.im := by
    have h1 : z.re ^ 2 - z.im ^ 2 = 0 := eq3 
    have h2 : (z.re - z.im) * (z.re + z.im) = 0 := by
      linarith [h1]
    cases (mul_eq_zero.1 h2) with
    | inl h3 =>
      left 
      linarith 
    | inr h4 =>
      right 
      linarith 
  cases eq6 with
  | inl h_eq =>
    have eq7 : z.re ^ 2 = 4 := by 
      have h_eq1 : z.im = z.re := by linarith 
      rw [show z.im = z.re by linarith] at eq4 
      nlinarith 
    have eq8 : z.re = 2 ∨ z.re = -2 := by 
      have h1 : z.re ^ 2 = 4 := eq7 
      have h2 : z.re ^ 2 - 4 = 0 := by linarith 
      have h3 : (z.re - 2) * (z.re + 2) = 0 := by 
        linarith [h2] 
      cases (mul_eq_zero.1 h3) with
      | inl h4 =>
        left 
        linarith 
      | inr h5 =>
        right 
        linarith 
    cases eq8 with
    | inl h_re =>
      have h_im : z.im = 2 := by 
        nlinarith [h_eq, h_re] 
      left 
      simp [Complex.ext_iff, h_re, h_im] 
    | inr h_re =>
      have h_im : z.im = -2 := by 
        nlinarith [h_eq, h_re] 
      right 
      simp [Complex.ext_iff, h_re, h_im] 
  | inr h_eq =>
    -- This leads to a contradiction 
    have eq8 : z.im ^ 2 = -4 := by 
      have h_eq1 : z.re = -z.im := h_eq 
      rw [show z.re = -z.im by linarith] at eq4 
      nlinarith 
    nlinarith [sq_nonneg (z.im)]