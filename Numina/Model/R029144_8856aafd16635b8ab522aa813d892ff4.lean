import Mathlib

theorem algebra_206500 (z : ℂ) (hz : Complex.abs (z - 5) = Complex.abs (z - 1) + 4) :
    ∃ r : ℝ, z = r := by
  have eq1 : Complex.abs (z - 5) = Real.sqrt ((z.re - 5) ^ 2 + (z.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have eq2 : Complex.abs (z - 1) = Real.sqrt ((z.re - 1) ^ 2 + (z.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [eq1, eq2] at hz
  have h1 : Real.sqrt ((z.re - 5) ^ 2 + z.im ^ 2) = Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) + 4 := hz
  have h2 : (Real.sqrt ((z.re - 5) ^ 2 + z.im ^ 2)) ^ 2 = (Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) + 4) ^ 2 := by
    rw [h1]
  have h3 : (Real.sqrt ((z.re - 5) ^ 2 + z.im ^ 2)) ^ 2 = (z.re - 5) ^ 2 + z.im ^ 2 := by
    apply Real.sq_sqrt
    positivity
  have h4 : (Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2)) ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    apply Real.sq_sqrt
    positivity
  have h32 : z.im = 0 := by 
    nlinarith [Real.sqrt_nonneg ((z.re - 5) ^ 2 + z.im ^ 2), Real.sqrt_nonneg ((z.re - 1) ^ 2 + z.im ^ 2), sq_nonneg (z.im), sq_nonneg ((z.re - 1 : ℝ) ^ 2 + (z.im) ^ 2), sq_nonneg ((z.re - 5) ^ 2 - (z.re - 1) ^ 2), mul_nonneg (Real.sqrt_nonneg ((z.re - 5) ^ 2 + z.im ^ 2)) (Real.sqrt_nonneg ((z.re - 1) ^ 2 + z.im ^ 2))]
  use z.re
  simp [Complex.ext_iff, h32]