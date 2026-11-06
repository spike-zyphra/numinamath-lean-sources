import Mathlib

theorem algebra_11319 (z1 z2 : ℂ) (hz1 : ‖z1‖ = 5) (hz2 : z1 / z2 = 2 + .I) :
    ‖z1 - z2‖ = Real.sqrt 10 := by
  have h1 : z2 ≠ 0 := by
    by_contra h
    rw [h] at hz2
    field_simp [Complex.ext_iff] at hz2
  have h3 : z1 = (2 + Complex.I) * z2 := by
    rw [← hz2]
    field_simp [h1]
  have h4 : ‖z1‖ = Real.sqrt 5 * ‖z2‖ := by
    rw [h3]
    have h5 : ‖(2 + Complex.I) * z2‖ = ‖(2 + Complex.I : ℂ)‖ * ‖z2‖ := by
      simp [norm_mul]
    rw [h5]
    have h6 : ‖(2 + Complex.I : ℂ)‖ = Real.sqrt 5 := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals
        ring_nf
    rw [h6]
  have h7 : ‖z2‖ = Real.sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have h8 : z1 - z2 = (1 + Complex.I) * z2 := by
    rw [h3]
    ring_nf
  have h9 : ‖z1 - z2‖ = ‖(1 + Complex.I) * z2‖ := by
    rw [h8]
  have h10 : ‖(1 + Complex.I) * z2‖ = ‖(1 + Complex.I : ℂ)‖ * ‖z2‖ := by
    simp [norm_mul]
  have h11 : ‖(1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    all_goals
      ring_nf
  rw [h10] at h9
  rw [h11] at h9
  have h12 : Real.sqrt 2 * ‖z2‖ = Real.sqrt 10 := by
    rw [h7]
    have h13 : Real.sqrt 2 * Real.sqrt 5 = Real.sqrt 10 := by
      calc
        Real.sqrt 2 * Real.sqrt 5 = Real.sqrt (2 * 5) := by rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt 10 := by norm_num
    linarith [h13]
  linarith [h12, h9]