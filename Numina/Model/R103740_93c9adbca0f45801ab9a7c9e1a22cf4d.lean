import Mathlib

theorem calculus_22500 (z : ℂ) (hz : z = -24 + 7 * .I) :
    Real.cos (Complex.arg z) = -24 / 25 := by
  rw [hz]
  have h_mod : Complex.abs (-24 + 7 * Complex.I) = 25 := by
    simp [Complex.abs, Complex.normSq]
    norm_num [Real.sqrt_eq_iff_sq_eq]
    <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : (-24 + 7 * Complex.I).re = Complex.abs (-24 + 7 * Complex.I) * Real.cos (Complex.arg (-24 + 7 * Complex.I)) := by
    simpa [Complex.re, Complex.im] using Complex.re_eq_abs_cos_arg (-24 + 7 * Complex.I)
  rw [h_mod] at h3
  norm_num [Complex.re] at h3 ⊢
  linarith