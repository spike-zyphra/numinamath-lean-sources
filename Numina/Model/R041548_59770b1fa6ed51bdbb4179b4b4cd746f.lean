import Mathlib

theorem algebra_57771 {z1 z2 : ℂ} (h : Complex.abs (z1 + 2 * z2) = Complex.abs (2 * z1 + z2)) (a : ℝ) :
    Complex.abs (z1 + a * z2) = Complex.abs (a * z1 + z2) := by
  have h1 : Complex.abs (z1 + 2 * z2) = Complex.abs (2 * z1 + z2) := h
  have eq1 : Complex.abs (z1 + 2 * z2) = Real.sqrt ((z1.re + 2 * z2.re)^2 + (z1.im + 2 * z2.im)^2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have eq2 : Complex.abs (2 * z1 + z2) = Real.sqrt ((2 * z1.re + z2.re)^2 + (2 * z1.im + z2.im)^2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [eq1] at h1 
  rw [eq2] at h1
  have h2 : ((z1.re + 2 * z2.re)^2 + (z1.im + 2 * z2.im)^2) = ((2 * z1.re + z2.re)^2 + (2 * z1.im + z2.im)^2) := by 
    have h_eq : (Real.sqrt ((z1.re + 2 * z2.re)^2 + (z1.im + 2 * z2.im)^2)) ^2 = (Real.sqrt ((2 * z1.re + z2.re)^2 + (2 * z1.im + z2.im)^2)) ^2 := by 
      rw [h1]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity) ] at h_eq
    nlinarith 
  have habs : z1.re ^ 2 + z1.im ^ 2 = z2.re ^ 2 + z2.im ^ 2 := by
    nlinarith 
  have h_eq1 : Complex.abs (z1 + a * z2) = Real.sqrt ((z1.re + a * z2.re) ^ 2 + (z1.im + a * z2.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have h_eq2 : Complex.abs (a * z1 + z2) = Real.sqrt ((a * z1.re + z2.re) ^ 2 + (a * z1.im + z2.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h_eq1, h_eq2]
  have eq3 : ((z1.re + a * z2.re) ^ 2 + (z1.im + a * z2.im) ^ 2) = ((a * z1.re + z2.re) ^ 2 + (a * z1.im + z2.im) ^ 2) := by
    nlinarith [habs, sq_nonneg (z1.re - z2.re), sq_nonneg (z1.im - z2.im), sq_nonneg (z1.re * z2.im - z1.im * z2.re), mul_nonneg (show (0 : ℝ) ≤ a ^ 2 by nlinarith) (show (0 : ℝ) ≤ 1 by nlinarith)]
  have eq4 : Real.sqrt ((z1.re + a * z2.re) ^ 2 + (z1.im + a * z2.im) ^ 2) = Real.sqrt ((a * z1.re + z2.re) ^ 2 + (a * z1.im + z2.im) ^ 2) := by
    rw [eq3]
  exact_mod_cast eq4