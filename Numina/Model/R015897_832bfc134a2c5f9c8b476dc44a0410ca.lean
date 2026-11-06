import Mathlib

theorem algebra_245551 {z1 z2 : ℂ} (h : Complex.abs (z1 + 2 * z2) = Complex.abs (2 * z1 + z2)) :
    ∀ α : ℝ, Complex.abs (z1 + α * z2) = Complex.abs (α * z1 + z2) := by
  intro α
  have h1 : Complex.abs (z1 + 2 * z2) = Complex.abs (2 * z1 + z2) := h
  have eq1 : Complex.abs (z1 + 2 * z2) = Real.sqrt ((z1 + 2 * z2).re ^ 2 + (z1 + 2 * z2).im ^ 2) := by 
    simp [Complex.abs, Complex.normSq]
    <;> ring
  have eq2 : Complex.abs (2 * z1 + z2) = Real.sqrt ((2 * z1 + z2).re ^ 2 + (2 * z1 + z2).im ^ 2) := by 
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [eq1] at h1
  rw [eq2] at h1
  have h5 : (z1 + 2 * z2).re ^ 2 + (z1 + 2 * z2).im ^ 2 = (2 * z1 + z2).re ^ 2 + (2 * z1 + z2).im ^ 2 := by
    have h6 : Real.sqrt ((z1 + 2 * z2).re ^ 2 + (z1 + 2 * z2).im ^ 2) = Real.sqrt ((2 * z1 + z2).re ^ 2 + (2 * z1 + z2).im ^ 2) := h1
    have h7 : (Real.sqrt ((z1 + 2 * z2).re ^ 2 + (z1 + 2 * z2).im ^ 2)) ^ 2 = (Real.sqrt ((2 * z1 + z2).re ^ 2 + (2 * z1 + z2).im ^ 2)) ^ 2 := by rw [h6]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)  ] at h7
    linarith
  have eq1' : z1.re ^ 2 + z1.im ^ 2 = z2.re ^ 2 + z2.im ^ 2 := by 
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_comm] at h5 ⊢
    nlinarith
  have eq3 : Complex.abs (z1 + ↑α * z2) = Real.sqrt ((z1 + ↑α * z2).re ^ 2 + (z1 + ↑α * z2).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  have eq4 : Complex.abs (↑α * z1 + z2) = Real.sqrt ((↑α * z1 + z2).re ^ 2 + (↑α * z1 + z2).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [eq3, eq4]
  have eq5 : (z1 + ↑α * z2).re ^ 2 + (z1 + ↑α * z2).im ^ 2 = (↑α * z1 + z2).re ^ 2 + (↑α * z1 + z2).im ^ 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_comm]
    <;> 
    ring_nf at *
    <;> 
    nlinarith [eq1']
  rw [eq5]
  all_goals norm_num [Real.sqrt_eq_iff_sq_eq, Real.sqrt_pow_two, Real.sqrt_nonneg, Real.sqrt_eq_iff_sq_eq, Real.sqrt_pow_two, Real.sqrt_nonneg]