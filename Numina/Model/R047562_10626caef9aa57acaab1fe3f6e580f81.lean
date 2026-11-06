import Mathlib

theorem algebra_134806 {a b : ℂ} (p : ℂ → ℂ) (hp : ∀ z, p z = z ^ 2 + a * z + b)
    (h : ∀ z, ‖z‖ = 1 → ‖p z‖ = 1) : a = 0 ∧ b = 0 := by
  have eq1 := h 1 (by simp [Complex.norm_eq_abs])
  have eq2 := h (-1 : ℂ) (by simp [Complex.norm_eq_abs])
  have eq3 := h (Complex.I) (by simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq])
  have eq4 := h (-Complex.I) (by simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq])
  simp [hp, Complex.norm_eq_abs, Complex.abs, Complex.normSq] at eq1 eq2 eq3 eq4
  ring_nf at eq1 eq2 eq3 eq4
  have eq5 := h ((1 : ℂ) / 2 * (Complex.I))
  have eq6 := h ((1 : ℂ) / 2 * (-Complex.I))
  have eq7 := h ((1 + Complex.I) / Real.sqrt 2)
  have eq8 := h ((1 - Complex.I) / Real.sqrt 2)
  simp [hp, Complex.norm_eq_abs, Complex.abs, Complex.normSq] at eq5 eq6 eq7 eq8
  ring_nf at eq5 eq6 eq7 eq8 
  have h1 : a = 0 := by
    simp [Complex.ext_iff]
    constructor
    · -- Show that the real part of a is zero
      nlinarith 
    · -- Show that the imaginary part of a is zero
      nlinarith 
  have h2 : b = 0 := by
    simp [Complex.ext_iff]
    constructor
    · -- Show that the real part of b is zero
      nlinarith 
    · -- Show that the imaginary part of b is zero
      nlinarith 
  exact ⟨h1, h2⟩