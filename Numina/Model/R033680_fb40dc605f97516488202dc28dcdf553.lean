import Mathlib

theorem algebra_9061 {a b : ℝ} (h : (a + 2 * Complex.I) / Complex.I = b + Complex.I) : a + b = 1 := by
  have h1 : (a + 2 * Complex.I) / Complex.I = (a + 2 * Complex.I) * (-Complex.I) := by
    field_simp [Complex.I_mul_I]
    <;> ring
  have h2 : (a + 2 * Complex.I) * (-Complex.I) = 2 - a * Complex.I := by
    simp [Complex.ext_iff, Complex.I_mul_I]
    all_goals ring
  rw [h1, h2] at h
  have h3 : (2 - a * Complex.I).re = (b + Complex.I).re := by
    rw [h]
  have h4 : (2 - a * Complex.I).im = (b + Complex.I).im := by
    rw [h]
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at h3 h4
  linarith