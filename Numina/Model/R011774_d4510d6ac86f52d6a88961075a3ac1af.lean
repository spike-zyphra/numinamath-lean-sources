import Mathlib

theorem algebra_150435 {z1 z2 : ℂ} (hz1 : ‖z1‖ = 1) (hz2 : ‖z2‖ = 1)
    (h : z1 + z2 = -7 / 5 + 1 / 5 * .I) :
    z1 * z2 = 24 / 25 - 7 / 25 * .I := by
  have h1 : ‖z1‖ = Real.sqrt ((z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring
  have h2 : ‖z2‖ = Real.sqrt ((z2.re : ℝ) ^ 2 + (z2.im : ℝ) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring
  rw [h1] at hz1
  rw [h2] at hz2
  have h3 : (z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2 = 1 := by 
    calc
      (z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2 = (Real.sqrt ((z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (1 : ℝ) ^ 2 := by rw [hz1]
      _ = (1 : ℝ) := by norm_num
  have h4 : (z2.re : ℝ) ^ 2 + (z2.im : ℝ) ^ 2 = 1 := by
    calc 
      (z2.re : ℝ) ^ 2 + (z2.im : ℝ) ^ 2 = (Real.sqrt ((z2.re : ℝ) ^ 2 + (z2.im : ℝ) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (1 : ℝ) ^ 2 := by rw [hz2]
      _ = (1 : ℝ) := by norm_num
  have h5 : z1.re + z2.re = -7 / 5 := by
    have h8 := congr_arg Complex.re h
    simp [Complex.add_re, Complex.ofReal_re, Complex.I_re] at h8 ⊢
    linarith
  have h6 : z1.im + z2.im = 1 / 5 := by
    have h9 := congr_arg Complex.im h
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at h9 ⊢
    linarith
  have h7 : z2.re = -7 / 5 - z1.re := by linarith
  have h8 : z2.im = 1 / 5 - z1.im := by linarith
  rw [h7, h8] at h4
  have eq1 : z1 * z2 = (z1.re * z2.re - z1.im * z2.im) + (z1.re * z2.im + z1.im * z2.re) * Complex.I := by
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    <;> ring
  rw [eq1]
  rw [show z2.re = -7 / 5 - z1.re by linarith, show z2.im = 1 / 5 - z1.im by linarith]
  simp [Complex.ext_iff]
  constructor
  · -- Real part
    field_simp
    nlinarith [sq_nonneg (z1.re + 3 / 5), sq_nonneg (z1.im + 4 / 5), sq_nonneg (z1.re + 4 / 5), sq_nonneg (z1.im - 3 / 5), Real.sqrt_nonneg ((z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2)]
  · -- Imaginary part
    field_simp
    nlinarith [sq_nonneg (z1.re + 3 / 5), sq_nonneg (z1.im + 4 / 5), sq_nonneg (z1.re + 4 / 5), sq_nonneg (z1.im - 3 / 5), Real.sqrt_nonneg ((z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2)]