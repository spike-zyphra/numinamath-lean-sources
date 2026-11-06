import Mathlib

theorem algebra_233221 (z : ℂ) (hz : Complex.abs z = 1) :
    Complex.abs (z - 2) * Complex.abs (z + 1)^2 ∈ Set.Icc 0 (3 * Real.sqrt 3) := by
  have h1 : 0 ≤ Complex.abs (z - 2) * Complex.abs (z + 1) ^ 2 := by
    positivity
  have h2 : Complex.abs (z - 2) * Complex.abs (z + 1) ^ 2 ≤ 3 * Real.sqrt 3 := by
    have h3 : z.re ^ 2 + z.im ^ 2 = 1 := by 
      have h3 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h3] at hz 
      have h4 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := hz
      have h5 : z.re ^ 2 + z.im ^ 2 = 1 := by 
        calc 
          z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by 
              rw [Real.sq_sqrt] 
              positivity
          _ = 1 ^ 2 := by 
            rw [h4]
          _ = (1 : ℝ) := by 
            norm_num 
      exact_mod_cast h5
    have h4 : Complex.abs (z - 2) = Real.sqrt ((z.re - 2) ^ 2 + z.im ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf 
    have h5 : Complex.abs (z + 1) = Real.sqrt ((z.re + 1) ^ 2 + z.im ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf 
    have h6 : Complex.abs (z + 1) ^ 2 = ((z.re + 1) ^ 2 + z.im ^ 2) := by 
      calc 
        Complex.abs (z + 1) ^ 2 = (Real.sqrt ((z.re + 1) ^ 2 + z.im ^ 2)) ^ 2 := by rw [h5]
        _ = ((z.re + 1) ^ 2 + z.im ^ 2) := by 
          rw [Real.sq_sqrt] 
          positivity
    have h7 : Complex.abs (z - 2) = Real.sqrt ((z.re - 2) ^ 2 + z.im ^ 2) := h4
    rw [h7, h6]
    have h8 : (z.re - 2) ^ 2 + z.im ^ 2 = 5 - 4 * z.re := by
      have h : z.re ^ 2 + z.im ^ 2 = 1 := h3
      nlinarith 
    have h9 : ((z.re + 1) ^ 2 + z.im ^ 2) = 2 + 2 * z.re := by
      have h : z.re ^ 2 + z.im ^ 2 = 1 := h3
      nlinarith 
    have h10 : Real.sqrt ((z.re - 2) ^ 2 + z.im ^ 2) = Real.sqrt (5 - 4 * z.re) := by
      rw [h8]
    have h11 : ((z.re + 1) ^ 2 + z.im ^ 2) = (2 + 2 * z.re) := h9
    rw [h10, h11]
    have h12 : -1 ≤ z.re ∧ z.re ≤ 1 := by
      constructor
      · nlinarith [sq_nonneg z.im, h3]
      · nlinarith [sq_nonneg z.im, h3]
    have h13 : Real.sqrt (5 - 4 * z.re) * (2 + 2 * z.re) ≤ 3 * Real.sqrt 3 := by
      nlinarith [sq_nonneg (z.re - (1 : ℝ) / 2), sq_nonneg (z.re + 1), sq_nonneg (z.re - 1), Real.sqrt_nonneg (5 - 4 * z.re), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 - 4 * z.re) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith), mul_nonneg (Real.sqrt_nonneg (5 - 4 * z.re)) (Real.sqrt_nonneg (3 : ℝ)), sq_nonneg (Real.sqrt (5 - 4 * z.re) - Real.sqrt 3), Real.sqrt_nonneg (z.re + 1)]
    linarith 
  constructor
  · -- Show 0 ≤ Complex.abs (z - 2) * Complex.abs (z + 1) ^ 2
    linarith [h1]
  · -- Show Complex.abs (z - 2) * Complex.abs (z + 1) ^ 2 ≤ 3 * Real.sqrt 3
    linarith [h2]