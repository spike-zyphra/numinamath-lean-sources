import Mathlib

theorem algebra_112536 (z1 z2 : ℂ) (hz1 : ‖z1 + z2‖ = Real.sqrt 3) (hz2 : ‖z1‖ = 1) (hz3 : ‖z2‖ = 1) :
    ‖z1 - z2‖ = 1 := by
  have h1 : ‖z1 + z2‖ = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h2 : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h3 : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h4 : ‖z1 - z2‖ = Real.sqrt ((z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  rw [h1] at hz1
  rw [h2] at hz2
  rw [h3] at hz3
  rw [h4] at *
  have h5 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = 3 := by
    calc
      (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = (Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (Real.sqrt 3) ^ 2 := by rw [hz1]
      _ = 3 := by
        norm_num
  have h6 : z1.re ^ 2 + z1.im ^ 2 = 1 := by
    calc 
      z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by 
        rw [Real.sq_sqrt]
        positivity
      _ = (1 : ℝ) ^ 2 := by 
        rw [hz2]
      _ = (1 : ℝ) := by 
        norm_num
  have h7 : z2.re ^ 2 + z2.im ^ 2 = 1 := by 
    calc 
      z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by 
        rw [Real.sq_sqrt]
        positivity
      _ = (1 : ℝ) ^ 2 := by 
        rw [hz3]
      _ = (1 : ℝ) := by 
        norm_num
  have h8 : (z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2 = 1 := by 
    nlinarith 
  rw [h8]
  rw [Real.sqrt_eq_cases]
  norm_num