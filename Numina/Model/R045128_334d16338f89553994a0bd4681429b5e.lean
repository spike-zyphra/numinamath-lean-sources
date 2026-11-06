import Mathlib

theorem algebra_20567 {z : ℂ} (hz : ‖z‖ = 1) :
    (starRingEnd ℂ) z = 1 / z := by

  have h1 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring

  have h2 : (z.re ^ 2 + z.im ^ 2) = 1 := by
    rw [h1] at hz
    have h3 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := hz
    have h4 : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 = 1 ^ 2 := by
      rw [h3]
    have h5 : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      apply Real.sq_sqrt
      positivity
    have h6 : (1 : ℝ) ^ 2 = 1 := by norm_num
    nlinarith [h4, h5, h6]

  have h3 : z.re ^ 2 + z.im ^ 2 = 1 := h2

  have h5 : z ≠ 0 := by
    by_contra h
    have h6 : ‖z‖ = 0 := by 
      simp [h]
    linarith

  have h4 : z * ((starRingEnd ℂ) z) = 1 := by
    simp [Complex.ext_iff] at *
    constructor
    · -- Real part
      nlinarith
    · -- Imaginary part
      ring_nf
      <;> nlinarith

  have h6 : (starRingEnd ℂ) z = 1 / z := by
    rw [← h4]
    field_simp [h5]

  exact h6