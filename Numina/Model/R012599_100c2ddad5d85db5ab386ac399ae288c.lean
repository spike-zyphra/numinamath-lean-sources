import Mathlib

theorem algebra_151666 (z1 z2 : ℂ) (h₀ : ‖z1‖ = 5) (h₁ : z1 / z2 = 2 + Complex.I) :
    ‖z1 - z2‖ = Real.sqrt 10 := by
  have h2 : z2 ≠ 0 := by 
    by_contra h
    have h3 : z1 / z2 = 0 := by
      field_simp [h]
    rw [h3] at h₁
    norm_num [Complex.ext_iff] at h₁
  have h3 : z1 = (2 + Complex.I) * z2 := by
    have h4 : z2 ≠ 0 := h2
    field_simp [h4] at h₁ ⊢
    <;> simpa using h₁
  have h4 : ‖z1‖ = ‖2 + Complex.I‖ * ‖z2‖ := by
    rw [h3]
    simp [norm_mul]
  have h5 : ‖2 + Complex.I‖ = Real.sqrt 5 := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
  have h6 : ‖z2‖ = Real.sqrt 5 := by
    rw [h5] at h4
    nlinarith [h₀, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h7 : z1 - z2 = (1 + Complex.I) * z2 := by 
    rw [h3]
    ring_nf
  have h8 : ‖z1 - z2‖ = ‖(1 + Complex.I)‖ * ‖z2‖ := by
    rw [h7]
    simp [norm_mul]
  have h9 : ‖(1 + Complex.I)‖ = Real.sqrt 2 := by 
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num 
  rw [h9, h6] at h8
  have h10 : Real.sqrt 2 * Real.sqrt 5 = Real.sqrt 10 := by
    rw [← Real.sqrt_mul (by norm_num)]
    all_goals norm_num
  linarith [h8, h10]