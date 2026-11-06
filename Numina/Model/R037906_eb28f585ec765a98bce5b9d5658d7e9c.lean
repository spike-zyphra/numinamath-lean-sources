import Mathlib

def f (u v : ℂ) := u.re * v.re + u.im * v.im * Complex.I

theorem algebra_95810 {z : ℂ} (hz : f z z = z ^ 2 + 40) :
    Complex.abs z = 5 * Real.sqrt 2 := by
  simp [pow_two, f, Complex.ext_iff] at hz 
  -- At this point, `hz` contains two equations: one for the real part and one for the imaginary part.

  have h1 : z.im ^ 2 = 40 := by 
    have h_eq1 := hz.1
    nlinarith

  have h2 : z.re * z.im = 20 := by 
    have h_eq2 := hz.2
    nlinarith [sq_nonneg z.re, sq_nonneg z.im, h1]

  have h3 : z.re ^ 2 = 10 := by
    have h4 : (z.re * z.im) ^ 2 = 400 := by
      rw [h2]
      norm_num
    have h5 : (z.re * z.im) ^ 2 = z.re ^ 2 * z.im ^ 2 := by
      ring
    rw [h5] at h4
    rw [h1] at h4
    nlinarith

  have h4 : z.re ^ 2 + z.im ^ 2 = 50 := by
    nlinarith [h1, h3]

  have h5 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h5]

  have h6 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 5 * Real.sqrt 2 := by
    rw [show z.re ^ 2 + z.im ^ 2 = (50 : ℝ) by linarith [h4]]
    have h7 : Real.sqrt (50 : ℝ) = 5 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h7]
  rw [h6]