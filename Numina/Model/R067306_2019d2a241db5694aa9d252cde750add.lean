import Mathlib

theorem algebra_166506 (z : ℂ) (hz : Complex.abs z = 1) (h : Complex.abs (z - 1.45) = 1.05) :
    (z.re : ℝ) = 20 / 29 := by
  have h1 : z.re^2 + z.im^2 = 1 := by 
    have h_abs : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [pow_two]
      <;> ring
    rw [h_abs] at hz 
    have h_eq : Real.sqrt (z.re^2 + z.im^2) = 1 := by 
      exact hz
    have h_sq : z.re^2 + z.im^2 = (1 : ℝ) ^ 2 := by 
      calc 
        z.re^2 + z.im^2 = (Real.sqrt (z.re^2 + z.im^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (1 : ℝ) ^ 2 := by rw [h_eq]
    nlinarith
  have h2 : (z.re - 1.45)^2 + z.im^2 = (1.05 : ℝ) ^ 2 := by 
    have h_abs : Complex.abs (z - 1.45) = Real.sqrt ((z.re - 1.45)^2 + z.im^2) := by 
      simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
      <;> ring_nf <;> simp [pow_two]
      <;> ring
      <;> simp [Complex.re, Complex.im]
      <;> ring_nf <;> simp [pow_two]
      <;> ring
    rw [h_abs] at h 
    have h_eq : Real.sqrt ((z.re - 1.45)^2 + z.im^2) = (1.05 : ℝ) := by 
      exact h
    have h_sq : (z.re - 1.45)^2 + z.im^2 = (1.05 : ℝ) ^ 2 := by 
      calc 
        (z.re - 1.45)^2 + z.im^2 = (Real.sqrt ((z.re - 1.45)^2 + z.im^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (1.05 : ℝ) ^ 2 := by rw [h_eq]
    linarith
  norm_num at h1 h2 
  nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]