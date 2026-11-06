import Mathlib

theorem algebra_10553 {z1 z2 : ℂ} (hz1 : ‖z1‖ = 2) (hz2 : ‖z2‖ = 3)
    (h : 3 * z1 - 2 * z2 = 3 / 2 - Complex.I) :
    z1 * z2 = -30 / 13 + 72 / 13 * Complex.I := by

  have h1 : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Complex.normSq] <;> ring
  
  have h2 : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Complex.normSq] <;> ring
  
  rw [h1] at hz1
  rw [h2] at hz2
  have h3 : z1.re ^ 2 + z1.im ^ 2 = 4 := by 
    calc
      z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 2^2 := by rw [hz1]
      _ = 4 := by norm_num
  
  have h4 : z2.re ^ 2 + z2.im ^ 2 = 9 := by
    calc
      z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 3^2 := by rw [hz2]
      _ = 9 := by norm_num
  
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im] at eq1 eq2
  
  have eq3 : z2.re = 3 / 2 * z1.re - 3 / 4 := by 
    nlinarith
  
  have eq4 : z2.im = 3 / 2 * z1.im + 1 / 2 := by 
    nlinarith
  
  have h5 : (3 / 2 * z1.re - 3 / 4) ^ 2 + (3 / 2 * z1.im + 1 / 2) ^ 2 = 9 := by 
    rw [eq3, eq4] at h4
    linarith
  
  have eq5 : z1 * z2 = -30 / 13 + 72 / 13 * Complex.I := by 
    simp [Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, eq3, eq4]
    constructor
    · -- Real part
      nlinarith [sq_nonneg (z1.re - 6/13), sq_nonneg (z1.im - 12/13), sq_nonneg (z1.re + 6/13), sq_nonneg (z1.im + 12/13)]
    · -- Imaginary part
      nlinarith [sq_nonneg (z1.re - 6/13), sq_nonneg (z1.im - 12/13), sq_nonneg (z1.re + 6/13), sq_nonneg (z1.im + 12/13)]
  
  exact_mod_cast eq5