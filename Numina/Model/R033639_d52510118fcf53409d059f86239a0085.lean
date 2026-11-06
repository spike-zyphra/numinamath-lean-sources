import Mathlib

theorem algebra_180779 (x : ℂ) (hx : x^3 = -8 * .I) :
    x = (Real.sqrt 3 - .I) ∨ x = 2 * .I ∨ x = (-Real.sqrt 3 - .I) := by 
  have eq1 := congr_arg Complex.re hx
  have eq2 := congr_arg Complex.im hx
  simp [pow_three, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2 
  ring_nf at eq1 eq2 
  have h1 : x.re = 0 ∨ x.re^2 = 3 * x.im^2 := by
    have h := eq1
    have : x.re * (x.re^2 - 3 * x.im^2) = 0 := by
      nlinarith 
    cases (mul_eq_zero.1 this) with
    | inl h2 => 
      left
      exact h2
    | inr h2 => 
      right
      linarith 
  cases h1 with
  | inl h1 =>
    -- Case 1: x.re = 0
    have h2 : x.im^3 = 8 := by
      rw [h1] at eq2
      nlinarith 
    have h3 : x.im = 2 := by
      have h4 : x.im^3 - 8 = 0 := by linarith
      have h5 : (x.im - 2) * (x.im^2 + 2 * x.im + 4) = 0 := by
        nlinarith 
      cases (mul_eq_zero.1 h5) with
      | inl h6 => 
        linarith 
      | inr h7 => 
        have : x.im^2 + 2 * x.im + 4 > 0 := by
          nlinarith [sq_nonneg (x.im + 1)]
        have : x.im^2 + 2 * x.im + 4 = 0 := by
          linarith 
        nlinarith
    have h4 : x = (2 * Complex.I) := by
      simp [Complex.ext_iff, h1, h3]
    right 
    left
    exact h4
  | inr h1 =>
    -- Case 2: x.re^2 = 3 * x.im^2 
    have h2 : x.im^3 = -1 := by 
      have h5 : 3 * x.re^2 * x.im - x.im^3 = -8 := by 
        linarith 
      rw [h1] at h5 
      linarith 
    have h3 : x.im = -1 := by
      have h4 : x.im^3 + 1 = 0 := by linarith 
      have h5 : (x.im + 1) * (x.im^2 - x.im + 1) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.1 h5) with
      | inl h6 => 
        linarith 
      | inr h7 => 
        have : x.im^2 - x.im + 1 > 0 := by
          nlinarith [sq_nonneg (x.im - 1/2)]
        have : x.im^2 - x.im + 1 = 0 := by
          linarith 
        nlinarith 
    have h4 : x.re^2 = 3 := by
      rw [h3] at h1 
      nlinarith 
    have h40 : x.re = Real.sqrt 3 ∨ x.re = -Real.sqrt 3 := by
      have h5 : x.re^2 - 3 = 0 := by
        linarith 
      have h6 : (x.re - Real.sqrt 3) * (x.re + Real.sqrt 3) = 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 3 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (3: ℝ) by norm_num)]
      cases (mul_eq_zero.1 h6) with
      | inl h7 => 
        left 
        linarith 
      | inr h8 => 
        right 
        linarith 
    cases h40 with
    | inl h7 =>
      have h8 : x = (Real.sqrt 3 - Complex.I) := by
        simp [Complex.ext_iff, h7, h3]
      left
      exact h8
    | inr h8 =>
      have h9 : x = (-Real.sqrt 3 - Complex.I) := by
        simp [Complex.ext_iff, h8, h3]
        <;> nlinarith
      right
      right
      exact h9