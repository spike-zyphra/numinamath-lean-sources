import Mathlib

theorem algebra_251448 {z : ℂ} (hz : z ≠ -3 + 2 * .I) (h : Complex.abs ((z - 2 + 3 * .I) / (z + 3 - 2 * .I)) = 1) :
    (z).im = (z).re := by
  have h2 : (z + 3 - 2 * Complex.I) ≠ 0 := by 
    intro h_eq
    have hz2 : z = -3 + 2 * Complex.I := by
      have eq1 := congr_arg Complex.re h_eq 
      have eq2 := congr_arg Complex.im h_eq
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2 
      have h_eq2 : z.re = (-3 : ℝ) := by linarith 
      have h_eq3 : z.im = (2 : ℝ) := by linarith 
      simp [Complex.ext_iff, h_eq2, h_eq3] 
    contradiction 
  have h3 : Complex.abs ((z - 2 + 3 * Complex.I) / (z + 3 - 2 * Complex.I)) =
      Complex.abs (z - 2 + 3 * Complex.I) / Complex.abs (z + 3 - 2 * Complex.I) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Complex.ext_iff, mul_add, mul_sub, pow_two]
    <;> ring 
    all_goals norm_num 
  rw [h3] at h 
  have h4 : Complex.abs (z - 2 + 3 * Complex.I) = Complex.abs (z + 3 - 2 * Complex.I) := by
    have h5 : Complex.abs (z + 3 - 2 * Complex.I) ≠ 0 := by
      by_contra h6
      have h7 : Complex.abs (z + 3 - 2 * Complex.I) = (0 : ℝ) := by linarith 
      have h8 : z + 3 - 2 * Complex.I = 0 := by
        have h9 : Complex.abs (z + 3 - 2 * Complex.I) = Real.sqrt ((z + 3 - 2 * Complex.I).re ^ 2 + (z + 3 - 2 * Complex.I).im ^ 2) := by 
          simp [Complex.abs, Complex.normSq]
          <;> ring_nf
        rw [h9] at h7 
        have eq1 : ((z + 3 - 2 * Complex.I).re ^ 2 + (z + 3 - 2 * Complex.I).im ^ 2) = (0 : ℝ) := by
          have h11 : Real.sqrt ((z + 3 - 2 * Complex.I).re ^ 2 + (z + 3 - 2 * Complex.I).im ^ 2) = (0 : ℝ) := by
            linarith [h7]
          have h12 : (z + 3 - 2 * Complex.I).re ^ 2 + (z + 3 - 2 * Complex.I).im ^ 2 = (0 : ℝ) := by
            calc
              (z + 3 - 2 * Complex.I).re ^ 2 + (z + 3 - 2 * Complex.I).im ^ 2 = (Real.sqrt ((z + 3 - 2 * Complex.I).re ^ 2 + (z + 3 - 2 * Complex.I).im ^ 2)) ^ 2 := by 
                rw [Real.sq_sqrt]
                positivity 
              _ = (0 : ℝ) ^ 2 := by 
                rw [h11] 
              _ = (0 : ℝ) := by norm_num 
          linarith 
        have h20 : (z + 3 - 2 * Complex.I).re = (0 : ℝ) := by nlinarith [sq_nonneg ((z + 3 - 2 * Complex.I).re), sq_nonneg ((z + 3 - 2 * Complex.I).im)]
        have h30 : (z + 3 - 2 * Complex.I).im = (0 : ℝ) := by nlinarith [sq_nonneg ((z + 3 - 2 * Complex.I).re), sq_nonneg ((z + 3 - 2 * Complex.I).im)]
        simp [Complex.ext_iff, h20, h30] 
      have hz2 : z = -3 + 2 * Complex.I := by
        have eq1 := congr_arg Complex.re h8
        have eq2 := congr_arg Complex.im h8
        simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2 
        have eq3 : z.re = (-3 : ℝ) := by linarith 
        have eq4 : z.im = (2 : ℝ) := by linarith 
        simp [Complex.ext_iff, eq3, eq4]
      contradiction 
      all_goals norm_num 
    have h6 : Complex.abs (z + 3 - 2 * Complex.I) ≠ 0 := h5 
    field_simp [h6] at h ⊢
    all_goals try linarith 
    all_goals norm_num at h ⊢ 
    all_goals tauto 
  have eq1 : Complex.abs (z - 2 + 3 * Complex.I) = Real.sqrt ((z.re - 2) ^ 2 + (z.im + 3) ^ 2) := by
    simp [Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> ring_nf <;> simp [Complex.ext_iff]
    all_goals ring 
  have eq2 : Complex.abs (z + 3 - 2 * Complex.I) = Real.sqrt ((z.re + 3) ^ 2 + (z.im - 2) ^ 2) := by 
    simp [Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> ring_nf <;> simp [Complex.ext_iff]
    all_goals ring 
  have eq3 : Real.sqrt ((z.re - 2) ^ 2 + (z.im + 3) ^ 2) = Real.sqrt ((z.re + 3) ^ 2 + (z.im - 2) ^ 2) := by 
    rw [eq1] at h4 
    rw [eq2] at h4 
    exact_mod_cast h4 
  have h7 : (z.re - 2) ^ 2 + (z.im + 3) ^ 2 = (z.re + 3) ^ 2 + (z.im - 2) ^ 2 := by
    have h11 : (z.re - 2 : ℝ) ^ 2 + (z.im + 3) ^ 2 ≥ 0 := by
      positivity 
    have h22 : (z.re + 3 : ℝ) ^ 2 + (z.im - 2) ^ 2 ≥ 0 := by
      positivity 
    have h55 : Real.sqrt ((z.re - 2) ^ 2 + (z.im + 3) ^ 2) = Real.sqrt ((z.re + 3) ^ 2 + (z.im - 2) ^ 2) := eq3
    have h66 : (z.re - 2) ^ 2 + (z.im + 3) ^ 2 = (z.re + 3) ^ 2 + (z.im - 2) ^ 2 := by
      calc
        (z.re - 2) ^ 2 + (z.im + 3) ^ 2 = (Real.sqrt ((z.re - 2) ^ 2 + (z.im + 3) ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith 
        _ = (Real.sqrt ((z.re + 3) ^ 2 + (z.im - 2) ^ 2)) ^ 2 := by 
          rw [h55] 
        _ = (z.re + 3) ^ 2 + (z.im - 2) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith 
    exact_mod_cast h66
  have h8 : z.im = z.re := by
    nlinarith 
  exact_mod_cast h8 
  all_goals norm_num 
  all_goals tauto