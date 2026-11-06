import Mathlib

theorem number_theory_244973 (f : ℂ → ℂ) (m n : ℂ) (hf : ∀ z, ‖z‖ = 1 → ‖f z‖ = 1)
    (h : ∀ z, f z = z ^ 2 + m * z + n) :
    m + n = 0 := by

  have h1 := hf 1 (by
    norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at h1

  have h2 := hf (-1 : ℂ) (by
    norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at h2

  have h3 := hf (Complex.I : ℂ) (by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at h3

  have h4 := hf (-Complex.I : ℂ) (by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at h4

  simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, h] at h1 h2 h3 h4
  ring_nf at h1 h2 h3 h4
  norm_num [Complex.ext_iff] at *
  constructor
  · -- Show that the real parts sum to 0
    nlinarith [sq_nonneg (m.re + n.re), sq_nonneg (m.im + n.im), sq_nonneg (n.re - 1), sq_nonneg (m.im), sq_nonneg (n.im)]
  · -- Show that the imaginary parts sum to 0
    nlinarith [sq_nonneg (m.re + n.re), sq_nonneg (m.im + n.im), sq_nonneg (n.re - 1), sq_nonneg (m.im), sq_nonneg (n.im)]