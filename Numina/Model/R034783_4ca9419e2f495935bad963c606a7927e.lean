import Mathlib

theorem algebra_326673 (z1 z2 : ℂ) (h₁ : Complex.abs z1 = 2 * Complex.abs z2) (h₂ : Complex.abs z1 = 2)
    (h₃ : Complex.abs (z1 + z2) = Real.sqrt 7) :
    Complex.abs (z1 - z2) = Real.sqrt 3 := by

  have h₄ : Complex.abs z2 = 1 := by
    have h₅ : Complex.abs z1 = 2 * Complex.abs z2 := h₁
    have h₆ : Complex.abs z1 = 2 := h₂
    rw [h₆] at h₅
    linarith

  have h5 : Complex.abs z1 = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf

  have h6 : Complex.abs z2 = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf

  have h7 : Complex.abs (z1 + z2) = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im]
    <;> ring_nf

  have h8 : Complex.abs (z1 - z2) = Real.sqrt ((z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq, Complex.sub_re, Complex.sub_im]
    <;> ring_nf

  rw [h5] at h₂
  have h9 : z1.re ^ 2 + z1.im ^ 2 = 4 := by
    have h10 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = (2 : ℝ) := by
      simpa using h₂
    have h11 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) ≥ 0 := by positivity
    have h12 : (2 : ℝ) ≥ 0 := by norm_num
    have h13 : (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 = (2 : ℝ) ^ 2 := by
      rw [h10]
    rw [Real.sq_sqrt (by positivity)] at h13
    nlinarith

  rw [h6] at h₄
  have h14 : z2.re ^ 2 + z2.im ^ 2 = 1 := by
    have h15 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = (1 : ℝ) := by
      simpa using h₄
    have h16 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) ≥ 0 := by positivity
    have h17 : (1 : ℝ) ≥ 0 := by norm_num
    have h18 : (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [h15]
    rw [Real.sq_sqrt (by positivity)] at h18
    nlinarith

  rw [h7] at h₃
  have h19 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = 7 := by
    have h20 : Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) = Real.sqrt 7 := by
      simpa using h₃
    have h21 : Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) = Real.sqrt 7 := h20
    have h22 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 ≥ (0 : ℝ) := by positivity
    have h23 : (7 : ℝ) ≥ (0 : ℝ) := by norm_num
    have h24 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = (7 : ℝ) := by
      rw [Real.sqrt_inj (by positivity) (by norm_num) ] at h21
      linarith
    linarith

  rw [h8]
  have h20 : (z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2 = 3 := by
    nlinarith
  rw [h20]
  all_goals norm_num