import Mathlib

theorem algebra_190121 {z : ℂ} (hz : z ≠ -1) (hzz : Complex.abs z = 1) :
    ∃ t : ℝ, z = (1 + Complex.I * t) / (1 - Complex.I * t) := by
  have h1 : z ≠ -1 := hz
  have h2 : Complex.abs z = 1 := hzz
  have h3 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h4 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h4] at h2
    have h5 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := by
      linarith
    have h6 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by rw [h5]
        _ = 1 := by norm_num
    linarith
  have h4 : z.re + 1 ≠ 0 := by
    by_contra h
    have h5 : z.re = -1 := by linarith
    have h6 : z.im ^ 2 = 0 := by
      have h11 : z.re ^ 2 + z.im ^ 2 = 1 := h3
      rw [show z.re = -1 by linarith] at h11
      nlinarith
    have h7 : z.im = 0 := by nlinarith
    have h8 : z = -1 := by
      simp [Complex.ext_iff, h5, h7]
    contradiction
  use z.im / (z.re + 1)
  field_simp [Complex.ext_iff, h4]
  constructor
  · -- Show that the real parts are equal
    nlinarith [h3]
  · -- Show that the imaginary parts are equal
    nlinarith [h3]