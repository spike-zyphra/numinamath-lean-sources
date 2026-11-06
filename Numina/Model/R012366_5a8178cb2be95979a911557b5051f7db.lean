import Mathlib

theorem algebra_249344 {z1 z2 : ℂ} (hz1 : ‖z1‖ = 5) (hz2 : z1 / z2 = 2 + .I) :
    ‖z1 - z2‖ = Real.sqrt 10 := by
  have hz2_ne_zero : z2 ≠ 0 := by
    by_contra h
    rw [h] at hz2
    field_simp [Complex.ext_iff] at hz2
  have h1 : z1 = z2 * (2 + Complex.I) := by
    have h' : z1 = z2 * (z1 / z2) := by
      field_simp [hz2_ne_zero]
      <;> ring_nf <;> norm_num [Complex.ext_iff]
    rw [h']
    rw [hz2]
    <;> ring_nf <;> norm_num [Complex.ext_iff]
  have h2 : ‖z2‖ = Real.sqrt 5 := by
    have h3 : ‖z1‖ = ‖z2‖ * ‖(2 + Complex.I : ℂ)‖ := by
      rw [h1]
      simp [norm_mul]
      all_goals try norm_num
    have h4 : ‖(2 + Complex.I : ℂ)‖ = Real.sqrt 5 := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      ring_nf
      <;> norm_num [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      all_goals try norm_num
    rw [h4] at h3
    rw [hz1] at h3
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h3 : z1 - z2 = z2 * (1 + Complex.I) := by
    rw [h1]
    ring_nf 
    <;> simp [Complex.ext_iff, mul_add, mul_assoc]
    <;> ring_nf
  have h4 : ‖z1 - z2‖ = ‖z2‖ * ‖(1 + Complex.I : ℂ)‖ := by
    rw [h3]
    simp [norm_mul]
    all_goals try norm_num
  have h5 : ‖(1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals try norm_num
  rw [h4, h5, h2]
  have h6 : Real.sqrt 5 * Real.sqrt 2 = Real.sqrt 10 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num 
  rw [h6]
  all_goals try norm_num