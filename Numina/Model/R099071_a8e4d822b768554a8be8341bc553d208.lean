import Mathlib

theorem algebra_120958 (z1 z2 : ℂ) :
    Complex.abs (z1 + z2) ^ 2 + Complex.abs (z1 - z2) ^ 2 =
    2 * Complex.abs z1 ^ 2 + 2 * Complex.abs z2 ^ 2 := by
  have h1 : Complex.abs (z1 + z2) = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [pow_two]
    <;> ring_nf
  have h2 : Complex.abs (z1 - z2) = Real.sqrt ((z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [pow_two]
    <;> ring_nf
  have h3 : Complex.abs z1 = Real.sqrt ((z1.re) ^ 2 + (z1.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [pow_two]
    <;> ring_nf
  have h4 : Complex.abs z2 = Real.sqrt ((z2.re) ^ 2 + (z2.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [pow_two]
    <;> ring_nf
  rw [h1, h2, h3, h4]
  have h5 : Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) ^ 2 = (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h6 : Real.sqrt ((z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2) ^ 2 = (z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h7 : Real.sqrt ((z1.re) ^ 2 + (z1.im) ^ 2) ^ 2 = (z1.re) ^ 2 + (z1.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h8 : Real.sqrt ((z2.re) ^ 2 + (z2.im) ^ 2) ^ 2 = (z2.re) ^ 2 + (z2.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [h5, h6, h7, h8]
  ring_nf