import Mathlib

theorem algebra_174237 (z1 z2 : ℂ) (hz1 : ‖z1‖ = 1) (hz2 : ‖z2‖ = 1)
    (h : z1 + z2 = (1 / 2) + (Real.sqrt 3 / 2) * .I) :
    ‖z1 - z2‖ = Real.sqrt 3 := by
  have hz1_eq : z1.re ^ 2 + z1.im ^ 2 = 1 := by
    have h_abs : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num 
    have h_eq : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = 1 := by 
      rw [h_abs] at hz1
      linarith 
    have h_sq : z1.re ^ 2 + z1.im ^ 2 = 1 := by
      calc 
        z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity 
        _ = 1 ^ 2 := by rw [h_eq]
        _ = 1 := by norm_num 
    linarith 
  have hz2_eq : z2.re ^ 2 + z2.im ^ 2 = 1 := by
    have h_abs : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num 
    have h_eq : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = 1 := by 
      rw [h_abs] at hz2
      linarith 
    have h_sq : z2.re ^ 2 + z2.im ^ 2 = 1 := by
      calc 
        z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity 
        _ = 1 ^ 2 := by rw [h_eq]
        _ = 1 := by norm_num 
    linarith 
  have h_re : z1.re + z2.re = 1 / 2 := by
    have h_eq : z1 + z2 = (1 / 2) + (Real.sqrt 3 / 2) * Complex.I := h 
    have h_re := congr_arg Complex.re h_eq 
    simp at h_re 
    linarith 
  have h_im : z1.im + z2.im = Real.sqrt 3 / 2 := by
    have h_eq : z1 + z2 = (1 / 2) + (Real.sqrt 3 / 2) * Complex.I := h 
    have h_im := congr_arg Complex.im h_eq 
    simp at h_im 
    linarith 
  have h_eq : ‖z1 - z2‖ = Real.sqrt ((z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2) := by 
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num 
    <;> ring_nf <;> norm_num 
    all_goals ring 
  rw [h_eq]
  have eq1 : z1.re ^ 2 + z1.im ^ 2 = 1 := by linarith [hz1_eq]
  have eq2 : z2.re ^ 2 + z2.im ^ 2 = 1 := by linarith [hz2_eq]
  have eq3 : z1.re + z2.re = 1 / 2 := by linarith [h_re]
  have eq4 : z1.im + z2.im = Real.sqrt 3 / 2 := by linarith [h_im]
  have h_dot : (z1.re * z2.re + z1.im * z2.im) = -1 / 2 := by
    have h_re_sum : z1.re + z2.re = 1 / 2 := eq3 
    have h_im_sum : z1.im + z2.im = Real.sqrt 3 / 2 := eq4 
    have h_sum_sq : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = (1 / 2) ^ 2 + (Real.sqrt 3 / 2) ^ 2 := by
      rw [h_re_sum, h_im_sum]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
      sq_nonneg (z1.re * z2.im), sq_nonneg (z1.im * z2.re)]
  have h_mod_sq : (z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2 = 3 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
      h_dot, eq1, eq2, eq3, eq4, sq_nonneg (z1.re), sq_nonneg (z1.im), sq_nonneg (z2.re), sq_nonneg (z2.im)]
  rw [h_mod_sq]
  all_goals norm_num 
  all_goals ring_nf <;> norm_num 
  all_goals linarith