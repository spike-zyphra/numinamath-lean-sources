import Mathlib

theorem algebra_323078 {z : ℂ} (h : z + Complex.abs z = 3 + Complex.I) :
    z = 4 / 3 + Complex.I := by

  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h

  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2

  have h1 : z.im = 1 := by linarith

  have h2 : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring

  rw [h2] at eq1
  rw [h1] at eq1

  have h3 : z.re + Real.sqrt (z.re^2 + (1 : ℝ) ^ 2) = 3 := by
    nlinarith

  have h4 : Real.sqrt (z.re^2 + (1 : ℝ) ^ 2) = 3 - z.re := by
    linarith [h3]

  have h5 : (3 - z.re) ≥ 0 := by 
    have h6 : Real.sqrt (z.re^2 + (1 : ℝ) ^ 2) ≥ 0 := by 
      positivity
    have h7 : 3 - z.re ≥ 0 := by linarith [h4, h6]
    linarith

  have h8 : (Real.sqrt (z.re^2 + (1 : ℝ) ^ 2)) ^ 2 = (3 - z.re) ^ 2 := by 
    rw [h4]
    all_goals nlinarith

  have h9 : (z.re ^ 2 + (1 : ℝ) ^ 2) = (3 - z.re) ^ 2 := by
    have h11 : (Real.sqrt (z.re ^ 2 + (1 : ℝ) ^ 2)) ^ 2 = z.re ^ 2 + (1 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    linarith [h8, h11]

  have h10 : z.re = (4 / 3 : ℝ) := by
    nlinarith

  have h11 : z = (4 / 3 + Complex.I) := by
    simp [Complex.ext_iff, h10, h1]

  exact h11