import Mathlib

theorem algebra_140172 (z1 z2 : ℂ) (h₁ : Complex.abs z1 = 2) (h₂ : Complex.abs z2 = 3)
    (h₃ : 3 * z1 - 2 * z2 = 3 / 2 - Complex.I) :
    z1 * z2 = -30 / 13 + 72 / 13 * Complex.I := by
  have h3 : 3 * z1.re - 2 * z2.re = 3 / 2 := by
    norm_num [Complex.ext_iff] at h₃ ⊢
    linarith [h₃]
  have h4 : 3 * z1.im - 2 * z2.im = -1 := by
    norm_num [Complex.ext_iff] at h₃ ⊢
    linarith [h₃]
  have h5 : z1.re ^ 2 + z1.im ^ 2 = 4 := by
    have h11 : Complex.abs z1 = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [pow_two]
      <;> ring_nf
    rw [h11] at h₁
    have h12 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = 2 := h₁
    have h13 : z1.re ^ 2 + z1.im ^ 2 = 4 := by
      calc
        z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = 2 ^ 2 := by
          rw [h12]
        _ = (4 : ℝ) := by
          norm_num
    linarith
  have h6 : z2.re ^ 2 + z2.im ^ 2 = 9 := by
    have h21 : Complex.abs z2 = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [pow_two]
      <;> ring_nf
    rw [h21] at h₂
    have h22 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = 3 := h₂
    have h23 : z2.re ^ 2 + z2.im ^ 2 = 9 := by
      calc
        z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = 3 ^ 2 := by
          rw [h22]
        _ = (9 : ℝ) := by
          norm_num
    linarith
  have eq3 : z1.re = (2 * z2.re + 3 / 2) / 3 := by 
    linarith [h3]
  have eq4 : z1.im = (2 * z2.im - 1) / 3 := by
    linarith [h4]
  have eq5 : ((2 * z2.re + 3 / 2) / 3) ^ 2 + ((2 * z2.im - 1) / 3) ^ 2 = 4 := by 
    rw [eq3, eq4] at h5
    linarith
  have eq6 : z1.re * z2.re - z1.im * z2.im = -30 / 13 := by
    rw [eq3, eq4]
    nlinarith [sq_nonneg (z2.re - 6 / 13), sq_nonneg (z2.im - 12 / 13), sq_nonneg (z2.re + 6 / 13), sq_nonneg (z2.im + 12 / 13)]
  have eq7 : z1.re * z2.im + z1.im * z2.re = 72 / 13 := by
    rw [eq3, eq4]
    nlinarith [sq_nonneg (z2.re - 6 / 13), sq_nonneg (z2.im - 12 / 13), sq_nonneg (z2.re + 6 / 13), sq_nonneg (z2.im + 12 / 13)]
  simp [Complex.ext_iff, eq6, eq7]
  all_goals
    nlinarith [sq_nonneg (z1.re * z2.re - z1.im * z2.im + 30 / 13), sq_nonneg (z1.re * z2.im + z1.im * z2.re - 72 / 13), sq_nonneg (z2.re - 6 / 13), sq_nonneg (z2.im - 12 / 13), h5, h6, eq3, eq4]