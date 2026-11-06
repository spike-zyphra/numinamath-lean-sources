import Mathlib

theorem algebra_127514 (e : ℝ) (he : e > 0) (h : ∀ z : ℂ, Complex.abs (z^2) + Complex.abs (z^2 - 1) = 7 ↔
    (z - 1)^2 + (z + 1)^2 = 4 * e^2) :
    e = 1 / 2 := by
  have h1 := h 2
  norm_num [Complex.abs, pow_two, Complex.normSq] at h1
  have h2 := h (Complex.I * Real.sqrt 3)
  have h3 : Complex.abs ((Complex.I * Real.sqrt 3)^2) = 3 := by
    have h4 : (Complex.I * Real.sqrt 3) ^ 2 = -3 := by
      simp [pow_two, Complex.ext_iff, mul_pow, Complex.I_mul_I, Real.sq_sqrt]
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h4]
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num
  
  have h32 : Complex.abs ((Complex.I * Real.sqrt 3)^2 - 1) = 4 := by
    have h4 : (Complex.I * Real.sqrt 3) ^ 2 - 1 = -4 := by
      have h41 : (Complex.I * Real.sqrt 3) ^ 2 = -3 := by
        simp [pow_two, Complex.ext_iff, mul_pow, Complex.I_mul_I, Real.sq_sqrt]
        <;> ring_nf <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h41]
      ring
    rw [h4]
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num
  
  rw [h3, h32] at h2
  simp [pow_two, Complex.ext_iff, mul_pow, Complex.I_mul_I] at h2
  <;> ring_nf at h2 <;> norm_num at h2 <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]