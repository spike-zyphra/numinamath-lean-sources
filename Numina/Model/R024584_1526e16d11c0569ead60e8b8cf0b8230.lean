import Mathlib

theorem algebra_170977 (z : ℂ) (hz : Complex.abs (z - 1) = 2) (hz' : Complex.abs (z^2 - 1) = 6) :
    z.re = 5 / 4 := by
  have h1 : Complex.abs (z - 1) = Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring_nf
    <;> norm_num
  have h2 : Complex.abs (z^2 - 1) = Real.sqrt ((z.re^2 - z.im^2 - 1) ^ 2 + (2 * z.re * z.im) ^ 2) := by
    have hz2_re : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
      simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, 
            Complex.I_re, Complex.I_im]
      <;> ring_nf
      <;> simp [Complex.I_sq]
      <;> ring
    have hz2_im : (z ^ 2).im = 2 * z.re * z.im := by
      simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, 
            Complex.I_re, Complex.I_im]
      <;> ring_nf
      <;> simp [Complex.I_sq]
      <;> ring
    simp [Complex.abs, Complex.normSq, hz2_re, hz2_im]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring_nf
    <;> norm_num
  rw [h1] at hz
  have eq1 : (z.re - 1) ^ 2 + z.im ^ 2 = 4 := by 
    calc
      (z.re - 1) ^ 2 + z.im ^ 2 = (Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2)) ^ 2 := by 
        rw [Real.sq_sqrt]
        positivity
      _ = 2 ^ 2 := by 
        rw [hz]
        all_goals norm_num
      _ = 4 := by 
        norm_num
  rw [h2] at hz'
  have eq2 : (z.re^2 - z.im^2 - 1) ^ 2 + (2 * z.re * z.im) ^ 2 = 36 := by
    calc
      (z.re^2 - z.im^2 - 1) ^ 2 + (2 * z.re * z.im) ^ 2 = (Real.sqrt ((z.re^2 - z.im^2 - 1) ^ 2 + (2 * z.re * z.im) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = 6 ^ 2 := by
        rw [hz']
        all_goals norm_num
      _ = 36 := by
        norm_num
  nlinarith [sq_nonneg (z.re - 5 / 4), sq_nonneg (z.im ^ 2), sq_nonneg (z.re^2 - 25 / 16), sq_nonneg (z.im), 
            sq_nonneg (z.re^2 - z.im^2 - 1), sq_nonneg (2 * z.re * z.im)]