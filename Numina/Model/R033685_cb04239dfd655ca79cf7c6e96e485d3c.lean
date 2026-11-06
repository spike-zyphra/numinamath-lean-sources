import Mathlib

theorem algebra_21543 (z : ℂ) (hz : z ^ 4 = 64 / 5 - 48 / 5 * .I) : ‖z‖ = 2 := by
  have h1 : ‖z ^ 4‖ = ‖(64 / 5 - 48 / 5 * Complex.I)‖ := by
    rw [hz]
  have h2 : ‖z ^ 4‖ = ‖z‖ ^ 4 := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq] -- This expands the norm of z^4 in terms of the square roots
    <;> ring_nf
    <;> norm_num
  have h3 : ‖(64 / 5 - 48 / 5 * Complex.I)‖ = (16 : ℝ) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq] -- Compute norm of the right side: simplifier does the calculation with square root
    ring_nf -- Simplify the calculation
    <;> norm_num [Real.sqrt_eq_iff_sq_eq] -- Verify square root of 256 is 16, makes square equations for verification
  rw [h2] at h1
  rw [h3] at h1
  have h4 : ‖z‖ ^ 4 = (16 : ℝ) := by
    norm_num at h1 ⊢
    linarith
  have h5 : ‖z‖ = (2 : ℝ) := by
    have h6 : ‖z‖ ≥ 0 := by
      apply norm_nonneg
    have h7 : ‖z‖ ^ 4 - (16 : ℝ) = 0 := by
      linarith
    have h8 : (‖z‖ ^ 2 - 4) * (‖z‖ ^ 2 + 4) = 0 := by
      ring_nf at h7 ⊢
      linarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · 
      have h11 : ‖z‖ ^ 2 - 4 = 0 := by
        linarith
      have h12 : ‖z‖ ^ 2 = 4 := by
        linarith
      have h13 : ‖z‖ = 2 := by
        nlinarith [h6]
      linarith
    · 
      have h14 : ‖z‖ ^ 2 + 4 = 0 := by
        linarith
      have h15 : ‖z‖ ^ 2 ≥ 0 := by
        nlinarith [h6]
      nlinarith
  linarith [h5]