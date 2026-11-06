import Mathlib

theorem algebra_4609 (z : ℂ) (hz : z ≠ 0) (h : Complex.abs (z - 4 / z) = 2) :
    Complex.abs z ≤ 1 + Real.sqrt 5 ∧ Complex.abs z ≥ 1 - Real.sqrt 5 := by
  have h1 : z ≠ 0 := hz
  have h2 : Complex.abs (z - 4 / z) = 2 := h
  have h3 : Complex.abs (z - 4 / z) = Complex.abs (z ^ 2 - 4) / Complex.abs z := by
    have h4 : z - 4 / z = (z ^ 2 - 4) / z := by
      field_simp [show z ≠ 0 by exact h1]
      <;> ring
    rw [h4]
    have h5 : Complex.abs ((z ^ 2 - 4) / z) = Complex.abs (z ^ 2 - 4) / Complex.abs z := by
      simp [Complex.abs, Complex.normSq]
    exact h5
  rw [h3] at h2
  have h5 : Complex.abs z > 0 := by
    have h6 : z ≠ 0 := h1
    have h7 : Complex.abs z ≥ 0 := by positivity
    by_contra h
    push_neg at h
    have h8 : Complex.abs z = 0 := by linarith
    have h9 : z = 0 := by
      have h9 : Complex.abs z = 0 := h8
      simpa using h9
    tauto
  have h4 : Complex.abs (z ^ 2 - 4) = 2 * Complex.abs z := by
    have h33 : Complex.abs (z ^ 2 - 4) / Complex.abs z = 2 := by
      linarith
    have h11 : Complex.abs z ≠ 0 := by
      have h10 : Complex.abs z > 0 := h5
      linarith
    field_simp at h33 ⊢
    linarith
  have eq1 : Complex.abs (z ^ 2 - 4) = Real.sqrt ((z.re ^ 2 - z.im ^ 2 - 4) ^ 2 + (2 * z.re * z.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq, pow_two, Complex.ext_iff, mul_add, sub_eq_add_neg]
    ring_nf
  have eq2 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    all_goals
      ring_nf
  rw [eq1, eq2] at h4
  have h5 : (z.re ^ 2 - z.im ^ 2 - 4) ^ 2 + (2 * z.re * z.im) ^ 2 = 4 * (z.re ^ 2 + z.im ^ 2) := by
    calc
      (z.re ^ 2 - z.im ^ 2 - 4) ^ 2 + (2 * z.re * z.im) ^ 2 = (Real.sqrt ((z.re ^ 2 - z.im ^ 2 - 4) ^ 2 + (2 * z.re * z.im) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (2 * Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [h4]
      _ = 4 * (Real.sqrt (z.re ^ 2 + z.im ^ 2) ^ 2) := by ring
      _ = 4 * (z.re ^ 2 + z.im ^ 2) := by rw [Real.sq_sqrt]; positivity
  -- We will prove the upper bound
  have h8 : Complex.abs z ≤ 1 + Real.sqrt 5 := by
    have h14 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := eq2
    rw [h14]
    have h7 : (z.re ^ 2 + z.im ^ 2) ≤ (1 + Real.sqrt 5) ^ 2 := by
      nlinarith [sq_nonneg (z.re ^ 2 + z.im ^ 2 - (1 + Real.sqrt 5) ^ 2), sq_nonneg (z.re ^ 2 - z.im ^ 2 - (Real.sqrt 5)), sq_nonneg (z.re * z.im), sq_nonneg (z.re ^ 2 + z.im ^ 2 - 4), sq_nonneg (z.re ^ 2 + z.im ^ 2 - (z.re ^ 2 - z.im ^ 2) - 4), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
    have h11 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≤ 1 + Real.sqrt 5 := by
      have h9 : z.re ^ 2 + z.im ^ 2 ≤ (1 + Real.sqrt 5) ^ 2 := h7
      have h15 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≤ Real.sqrt ((1 + Real.sqrt 5) ^ 2) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h16 : Real.sqrt ((1 + Real.sqrt 5) ^ 2) = (1 + Real.sqrt 5 : ℝ) := by
        rw [Real.sqrt_sq (show (0 : ℝ) ≤ 1 + Real.sqrt 5 by
          have h5 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
          positivity
        )]
      linarith
    linarith
  -- We will prove the lower bound
  have h9 : Complex.abs z ≥ 1 - Real.sqrt 5 := by
    have h14 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := eq2
    rw [h14]
    have h11 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≥ (1 - Real.sqrt 5 : ℝ) := by
      have h10 : (z.re ^ 2 + z.im ^ 2) ≥ (1 - Real.sqrt 5) ^ 2 := by
        nlinarith [sq_nonneg (z.re ^ 2 + z.im ^ 2 - (1 - Real.sqrt 5) ^ 2), sq_nonneg (z.re ^ 2 - z.im ^ 2 - (Real.sqrt 5)), sq_nonneg (z.re * z.im), sq_nonneg (z.re ^ 2 + z.im ^ 2 - 4), sq_nonneg (z.re ^ 2 + z.im ^ 2 - (z.re ^ 2 - z.im ^ 2) - 4), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
      have h11 : (1 - Real.sqrt 5 : ℝ) ≤ Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
        have h100 : (1 - Real.sqrt 5 : ℝ) ≤ 0 := by
          have h10 : Real.sqrt 5 ≥ 1 := by
            have h2 : Real.sqrt 5 ≥ Real.sqrt 1 := by
              apply Real.sqrt_le_sqrt
              norm_num
            have h9 : Real.sqrt 1 = (1 : ℝ) := by rw [Real.sqrt_one]
            linarith [h2, h9]
          linarith
        have h101 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≥ 0 := by positivity
        have h14 : (1 - Real.sqrt 5 : ℝ) ≤ Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
          nlinarith [Real.sqrt_nonneg (z.re ^ 2 + z.im ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ z.re ^ 2 + z.im ^ 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
        linarith
      linarith
    linarith
  constructor
  · exact h8
  · exact h9