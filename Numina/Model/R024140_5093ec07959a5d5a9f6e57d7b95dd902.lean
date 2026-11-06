import Mathlib

theorem algebra_12887 {x : ℂ} (hx : x * (x - 2 * Real.sqrt 2 * .I) = 4) :
    ∃ A B C D : ℝ, x = A + B * .I ∨ x = C + D * .I ∧ A = Real.sqrt 2 ∧ B = Real.sqrt 2 ∧ C = -Real.sqrt 2 ∧ D = Real.sqrt 2 := by
  have eq1 := congr_arg Complex.re hx
  have eq2 := congr_arg Complex.im hx
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_assoc] at eq1 eq2
  have h1 : x.re ^ 2 - x.im ^ 2 + 2 * Real.sqrt 2 * x.im = 4 := by nlinarith
  have h2 : 2 * x.re * x.im - 2 * Real.sqrt 2 * x.re = 0 := by nlinarith
  have h3 : x.re * (x.im - Real.sqrt 2) = 0 := by 
    nlinarith 
  cases (mul_eq_zero.1 h3) with
  | inl h4 =>
    -- Assume x.re = 0
    have h4' : x.re = 0 := by
      simpa using h4
    rw [h4'] at h1
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), sq_nonneg (x.im)]
  | inr h5 =>
    have h5' : x.im = Real.sqrt 2 := by 
      linarith
    rw [h5'] at h1 
    have h6 : x.re ^ 2 = 2 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h7 : x.re = Real.sqrt 2 ∨ x.re = - Real.sqrt 2 := by 
      have h8 : x.re ^ 2 = 2 := h6
      have h9 : x.re ^ 2 - (2 : ℝ) = 0 := by linarith
      have h10 : (x.re - Real.sqrt 2) * (x.re + Real.sqrt 2) = 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases (mul_eq_zero.1 h10) with
      | inl h11 =>
        left
        linarith
      | inr h12 =>
        right
        linarith
    cases h7 with
    | inl h8 =>
      use Real.sqrt 2, Real.sqrt 2, -Real.sqrt 2, Real.sqrt 2
      left 
      simp [Complex.ext_iff, h8, h5']
      all_goals norm_num 
    | inr h9 =>
      use Real.sqrt 2, Real.sqrt 2, -Real.sqrt 2, Real.sqrt 2
      right 
      constructor
      · simp [Complex.ext_iff, h9, h5']
      all_goals norm_num