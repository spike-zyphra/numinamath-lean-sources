import Mathlib

theorem algebra_34225 {a b : ℂ} (P : ℂ → ℂ) (hP : ∀ z, P z = z ^ 2 + a * z + b)
    (hP' : ∀ z, ‖z‖ = 1 → ‖P z‖ = 1) : a = 0 ∧ b = 0 := by

  have eq1 := hP' 1 (by norm_num [Complex.norm_eq_abs])
  have eq2 := hP' (Complex.I) (by norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq])
  have eq3 := hP' (-1) (by norm_num [Complex.norm_eq_abs])
  have eq4 := hP' (-Complex.I) (by norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq])

  simp [hP, Complex.norm_eq_abs, Complex.abs, Complex.normSq] at eq1 eq2 eq3 eq4

  have eq11 : a.im * b.im = 0 := by
    ring_nf at eq2 eq4
    nlinarith

  have eq12 : a.im = 0 ∨ b.im = 0 := by
    cases (mul_eq_zero.mp eq11) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith

  rcases eq12 with (h | h)
  · -- a.im = 0
    have him : a.im = 0 := h 
    have h3 : a.re = 0 := by 
      ring_nf at eq1 eq2 eq3 eq4
      simp [him] at eq1 eq2 eq3 eq4
      nlinarith [sq_nonneg (a.re), sq_nonneg (b.re), sq_nonneg (b.im)]

    have ha : a = 0 := by
      simp [Complex.ext_iff, h3, him]

    have h4 : b.re = 0 := by 
      ring_nf at eq1 eq2 eq3 eq4 
      simp [him, h3] at eq1 eq2 eq3 eq4 
      nlinarith [sq_nonneg (b.im)]

    have h5 : b.im = 0 := by 
      ring_nf at eq1 eq2 eq3 eq4 
      simp [him, h3] at eq1 eq2 eq3 eq4 
      nlinarith [h4]

    have hb : b = 0 := by 
      simp [Complex.ext_iff, h4, h5]

    exact ⟨ha, hb⟩

  · -- b.im = 0 
    have him : b.im = 0 := h
    have h3 : a.re = 0 := by
      ring_nf at eq1 eq2 eq3 eq4 
      simp [him] at eq1 eq2 eq3 eq4 
      nlinarith [sq_nonneg (a.im), sq_nonneg (b.re), sq_nonneg (a.re)]

    have h4 : a.im = 0 := by 
      ring_nf at eq1 eq2 eq3 eq4
      simp [h3] at eq1 eq2 eq3 eq4 
      nlinarith [sq_nonneg (a.im), sq_nonneg (b.re), sq_nonneg (b.im)]

    have ha : a = 0 := by 
      simp [Complex.ext_iff, h3, h4]

    have h5 : b.re = 0 := by 
      ring_nf at eq1 eq2 eq3 eq4 
      simp [h3, h4, him] at eq1 eq2 eq3 eq4 
      nlinarith [sq_nonneg (a.im), sq_nonneg (b.re), sq_nonneg (b.im)]

    have hb : b = 0 := by 
      simp [Complex.ext_iff, h5, him]

    exact ⟨ha, hb⟩