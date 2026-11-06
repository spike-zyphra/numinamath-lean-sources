import Mathlib

theorem algebra_235025 {z : ℂ} (hz : Complex.abs z - z = 3 - .I) :
    z = -4 / 3 + .I := by
  have h1 : z.im = 1 := by
    have eq1 := congr_arg Complex.im hz
    simp [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.I_im] at eq1
    linarith
  have h2 : Complex.abs z = z.re + 3 := by
    have eq1 := congr_arg Complex.re hz
    simp [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re] at eq1
    linarith
  have h3 : z.re = -4 / 3 := by
    have eq1 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring
    rw [eq1] at h2
    rw [show z.im = (1 : ℝ) by linarith [h1] ] at h2
    have h4 : Real.sqrt (z.re ^ 2 + (1 : ℝ) ^ 2) = z.re + 3 := by
      linarith [h2]
    have h5 : z.re ^ 2 + (1 : ℝ) ^ 2 = (z.re + 3) ^ 2 := by
      calc
        z.re ^ 2 + (1 : ℝ) ^ 2 = (Real.sqrt (z.re ^ 2 + (1 : ℝ) ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (z.re + 3) ^ 2 := by
          rw [h4]
          <;> nlinarith
    nlinarith [Real.sqrt_nonneg (z.re ^ 2 + (1 : ℝ) ^ 2)]
  have h5 : z = -4 / 3 + Complex.I := by
    rw [Complex.ext_iff]
    constructor
    · -- Real part
      simp [h3]
    · -- Imaginary part
      simp [h1]
  exact h5