import Mathlib

theorem algebra_310393 : ¬∃ z : ℂ, ‖z‖ = 1 ∧ z^4 + z = 1 := by
  rintro ⟨z, h1, h2⟩
  have h3 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h3 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals ring
    rw [h3] at h1
    have h4 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := h1
    have h5 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by rw [h4]
        _ = (1 : ℝ) := by norm_num
    linarith

  have h4 : z ^ 4 = 1 - z := by 
    calc
      z ^ 4 = (z ^ 4 + z) - z := by ring
      _ = 1 - z := by rw [h2]

  have h9 : ‖(z : ℂ)‖ = 1 := by
    have h99 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals ring
    rw [h99] at h1
    have h11 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := h1
    have h12 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by rw [h11]
        _ = (1 : ℝ) := by norm_num
    -- simplify
    have h99 : ‖(z : ℂ)‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals ring
    rw [h99]
    linarith

  have h8 : ‖(z ^ 4 : ℂ)‖ = ‖(z : ℂ)‖ ^ 4 := by
    simp [norm_pow]

  have h7 : ‖(z ^ 4 : ℂ)‖ = ‖(1 - z : ℂ)‖ := by
    rw [h4]

  have h11 : Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) = 1 := by
    have h8' : ‖(z ^ 4 : ℂ)‖ = ‖(1 - z : ℂ)‖ := h7
    rw [h8] at h8'
    rw [h9] at h8'
    have h10 : ‖(1 - z : ℂ)‖ = Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, sub_eq_add_neg, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      all_goals ring
    rw [h10] at h8'
    nlinarith

  have h12 : (z.re - 1) ^ 2 + z.im ^ 2 = 1 := by
    calc
      (z.re - 1) ^ 2 + z.im ^ 2 = (Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 1 ^ 2 := by rw [h11]
      _ = (1 : ℝ) := by norm_num

  have h13 : z.re = 1 / 2 := by
    nlinarith

  have h14 : z.im ^ 2 = 3 / 4 := by
    nlinarith

  have h31 : z ^ 4 + z = 1 := h2
  have eq1 := congr_arg Complex.re h31
  have eq2 := congr_arg Complex.im h31
  simp [pow_two, pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h13, h14] at eq1 eq2
  ring_nf at eq1 eq2
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]