import Mathlib

theorem algebra_15957 {z : ℂ} (hz : ‖z‖ = 13) : z * (z.re - Complex.I * z.im) = 169 := by
  have h1 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring
  rw [h1] at hz
  have h2 : z.re ^ 2 + z.im ^ 2 = 169 := by
    have h3 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = (13 : ℝ) := hz
    have h4 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ^ 2 = (13 : ℝ) ^ 2 := by rw [h3]
    rw [Real.sq_sqrt (by positivity)] at h4
    norm_num at h4 ⊢
    linarith
  simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  <;> ring_nf
  <;> norm_num [h2] 
  <;> nlinarith