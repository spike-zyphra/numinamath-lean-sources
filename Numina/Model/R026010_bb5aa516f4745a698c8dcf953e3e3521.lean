import Mathlib

theorem algebra_313795 : ¬∃ z : ℂ, z ^ 4 + z = 1 ∧ ‖z‖ = 1 := by
  rintro ⟨z, h_eq, h_abs⟩
  have h1 : Complex.abs z = 1 := by
    simpa using h_abs
  have h2 : z ^ 4 = 1 - z := by
    have h : z ^ 4 + z = 1 := by
      simpa using h_eq
    calc
      z ^ 4 = (z ^ 4 + z) - z := by ring
      _ = 1 - z := by rw [h]
  have h3 : Complex.abs (z ^ 4) = Complex.abs (1 - z) := by
    rw [h2]
  have h4 : Complex.abs (z ^ 4) = Complex.abs z ^ 4 := by
    simp [Complex.abs_pow]
  have h5 : Complex.abs (1 - z) = 1 := by
    rw [h4] at h3
    rw [h1] at h3
    nlinarith
  have h6 : Complex.abs (1 - z) = 1 := h5
  have h7 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h8 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h8] at h1
    have h9 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := by
      linarith
    have h10 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (1 : ℝ) ^ 2 := by
          rw [h9]
        _ = (1 : ℝ) := by
          norm_num
    linarith
  have h8 : (1 - z.re) ^ 2 + z.im ^ 2 = 1 := by
    have h9 : Complex.abs (1 - z) = Real.sqrt ((1 - z.re) ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h9] at h6
    have h10 : Real.sqrt ((1 - z.re) ^ 2 + z.im ^ 2) = 1 := by
      linarith
    have h11 : (1 - z.re) ^ 2 + z.im ^ 2 = 1 := by
      calc
        (1 - z.re) ^ 2 + z.im ^ 2 = (Real.sqrt ((1 - z.re) ^ 2 + z.im ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (1 : ℝ) ^ 2 := by
          rw [h10]
        _ = (1 : ℝ) := by
          norm_num
    linarith
  have h7' : z.re = 1 / 2 := by
    nlinarith
  have h8' : z.im ^ 2 = 3 / 4 := by
    rw [h7'] at h7
    nlinarith
  have h9' : z.im = Real.sqrt 3 / 2 ∨ z.im = -Real.sqrt 3 / 2 := by
    have h9'' : z.im ^ 2 - 3 / 4 = 0 := by
      linarith
    have h10'' : z.im ^ 2 - 3 / 4 = (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h10''] at h9''
    cases (mul_eq_zero.mp h9'') with
    | inl h22 =>
      left
      linarith
    | inr h11 =>
      right
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h10 : z ^ 4 + z = 1 := by
    simpa using h_eq
  have h11 : z = 1 / 2 + Complex.I * (Real.sqrt 3 / 2) ∨ z = 1 / 2 + Complex.I * (-Real.sqrt 3 / 2) := by
    cases h9' with
    | inl h11 =>
      left
      simp [Complex.ext_iff, h7', h11]
    | inr h11 =>
      right
      simp [Complex.ext_iff, h7', h11]
  cases h11 with
  | inl h11 =>
    rw [h11] at h10
    have h12 : (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) ^ 3 = -1 := by
      simp [pow_three]
      field_simp [Complex.ext_iff, mul_add, pow_two, Complex.I_mul_I, mul_comm]
      ring_nf
      norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), mul_add, mul_comm]
    have h13 : (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) ^ 4 = - (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) := by
      calc
        (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) ^ 4
          = ((1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) ^ 3) * (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) := by ring
        _ = (-1) * (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) := by rw [h12]
        _ = - (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) := by ring
    have h14 : (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) ^ 4 + (1 / 2 + Complex.I * (Real.sqrt 3 / 2) : ℂ) = 0 := by
      rw [h13]
      ring
    norm_num [h14] at h10
  | inr h11 =>
    rw [h11] at h10
    have h12 : (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) ^ 3 = -1 := by
      simp [pow_three]
      field_simp [Complex.ext_iff, mul_add, pow_two, Complex.I_mul_I, mul_comm]
      ring_nf
      norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), mul_add, mul_comm]
    have h13 : (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) ^ 4 = - (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) := by
      calc
        (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) ^ 4
          = ((1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) ^ 3) * (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) := by ring
        _ = (-1) * (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) := by rw [h12]
        _ = - (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) := by ring
    have h14 : (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) ^ 4 + (1 / 2 + Complex.I * (-Real.sqrt 3 / 2) : ℂ) = 0 := by
      rw [h13]
      ring
    norm_num [h14] at h10