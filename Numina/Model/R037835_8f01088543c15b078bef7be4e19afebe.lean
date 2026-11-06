import Mathlib

open Complex


theorem algebra_307955 {z : ℂ} (hz : ‖z‖ = 1) (hz' : z ≠ -1) :
    ∃ t : ℝ, z = (1 + t * .I) / (1 - t * .I) := by
  have h1 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h_abs : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals
        ring_nf
    rw [h_abs] at hz
    have h2 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := hz
    have h3 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by rw [h2]
        _ = (1 : ℝ) := by norm_num
    linarith

  have h3 : z.re + 1 ≠ 0 := by
    by_contra h
    have h4 : z.re = -1 := by linarith
    have h5 : z.im ^ 2 = 0 := by
      have h1' : z.re ^ 2 + z.im ^ 2 = 1 := h1
      rw [show z.re = -1 by linarith [h4]] at h1'
      nlinarith
    have h6 : z.im = 0 := by
      nlinarith
    have h7 : z = -1 := by
      simp [Complex.ext_iff, h4, h6]
    contradiction

  use z.im / (z.re + 1)
  field_simp [Complex.ext_iff, h3]
  constructor
  · -- Show equality for real parts
    have h4 : z.re ^ 2 + z.im ^ 2 = 1 := h1
    nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]
  · -- Show equality for imaginary parts
    have h4 : z.re ^ 2 + z.im ^ 2 = 1 := h1
    nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]