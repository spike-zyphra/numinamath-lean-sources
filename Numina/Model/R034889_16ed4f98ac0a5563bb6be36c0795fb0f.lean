import Mathlib


theorem algebra_276446 : ¬∃ z : ℂ, z ^ 4 + z = 1 ∧ ‖z‖ = 1 := by
  rintro ⟨z, h_eq, h_abs⟩
  have h1 : z ^ 4 + z = 1 := h_eq
  have h2 : ‖z‖ = 1 := h_abs
  have h3 : z ^ 4 = 1 - z := by
    calc
      z ^ 4 = (z ^ 4 + z) - z := by ring_nf
      _ = 1 - z := by rw [h1]
  have h4 : ‖z ^ 4‖ = ‖(1 - z : ℂ)‖ := by
    rw [h3]
  have h5 : ‖z ^ 4‖ = ‖z‖ ^ 4 := by
    simp [norm_pow]
  have h6 : ‖(1 - z : ℂ)‖ = 1 := by
    calc
      ‖(1 - z : ℂ)‖ = ‖z ^ 4‖ := by rw [h4]
      _ = ‖z‖ ^ 4 := by rw [h5]
      _ = (1 : ℝ) ^ 4 := by rw [h2]
      _ = (1 : ℝ) := by norm_num
  have h8 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h9 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals
        ring_nf
    rw [h9] at h2
    have h10 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := by
      linarith
    have h11 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (1 : ℝ) ^ 2 := by rw [h10]
        _ = (1 : ℝ) := by norm_num
    linarith
  have h10 : (1 - z.re) ^ 2 + z.im ^ 2 = 1 := by
    have h11 : ‖(1 - z : ℂ)‖ = Real.sqrt ((1 - z.re) ^ 2 + z.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.ext_iff, sub_eq_zero]
      all_goals
        ring_nf
    rw [h11] at h6
    have h12 : Real.sqrt ((1 - z.re) ^ 2 + z.im ^ 2) = 1 := by
      linarith
    have h13 : (1 - z.re) ^ 2 + z.im ^ 2 = 1 := by
      calc
        (1 - z.re) ^ 2 + z.im ^ 2 = (Real.sqrt ((1 - z.re) ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (1 : ℝ) ^ 2 := by rw [h12]
        _ = (1 : ℝ) := by norm_num
    linarith
  have h11 : z.re = 1 / 2 := by
    nlinarith
  have h12 : z.im ^ 2 = 3 / 4 := by
    rw [show z.re = 1 / 2 by linarith [h11]] at h8
    nlinarith
  have h13 : z = 1 / 2 + Complex.I * (z.im) := by
    simp [Complex.ext_iff, h11]
  rw [h13] at h1
  simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h1
  ring_nf at h1
  nlinarith [sq_nonneg (z.im), sq_nonneg (z.im ^ 2 - 3 / 4)]