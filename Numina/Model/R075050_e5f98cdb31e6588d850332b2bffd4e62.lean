import Mathlib

theorem algebra_103853 {z1 z2 : ℂ} :
    4 * Complex.abs (z1 + z2) ^ 2 + Complex.abs (z1 - 2 * z2) ^ 2 +
    Complex.abs (-2 * z1 + z2) ^ 2 = 9 * Complex.abs z1 ^ 2 + 9 * Complex.abs z2 ^ 2 := by 
  have h1 : Complex.abs (z1 + z2) ^ 2 = (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 := by
    have h_abs : Complex.abs (z1 + z2) = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [pow_two]
      <;> ring
    rw [h_abs]
    rw [Real.sq_sqrt]
    positivity

  have h2 : Complex.abs (z1 - 2 * z2) ^ 2 = (z1.re - 2 * z2.re) ^ 2 + (z1.im - 2 * z2.im) ^ 2 := by
    have h_abs : Complex.abs (z1 - 2 * z2) = Real.sqrt ((z1.re - 2 * z2.re) ^ 2 + (z1.im - 2 * z2.im) ^ 2) := by
      simp [Complex.abs, Complex.normSq, mul_add, mul_sub]
      all_goals ring_nf <;> simp [pow_two]
      <;> ring
    rw [h_abs]
    rw [Real.sq_sqrt]
    positivity

  have h3 : Complex.abs (-2 * z1 + z2) ^ 2 = (-2 * z1.re + z2.re) ^ 2 + (-2 * z1.im + z2.im) ^ 2 := by
    have h_abs : Complex.abs (-2 * z1 + z2) = Real.sqrt ((-2 * z1.re + z2.re) ^ 2 + (-2 * z1.im + z2.im) ^ 2) := by
      simp [Complex.abs, Complex.normSq, mul_add, mul_sub]
      all_goals ring_nf <;> simp [pow_two]
      <;> ring
    rw [h_abs]
    rw [Real.sq_sqrt]
    positivity

  have h4 : Complex.abs z1 ^ 2 = z1.re ^ 2 + z1.im ^ 2 := by
    have h_abs : Complex.abs z1 = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      all_goals ring_nf <;> simp [pow_two]
      <;> ring
    rw [h_abs]
    rw [Real.sq_sqrt]
    positivity

  have h5 : Complex.abs z2 ^ 2 = z2.re ^ 2 + z2.im ^ 2 := by
    have h_abs : Complex.abs z2 = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      all_goals ring_nf <;> simp [pow_two]
      <;> ring
    rw [h_abs]
    rw [Real.sq_sqrt]
    positivity
  
  rw [h1, h2, h3, h4, h5]
  ring