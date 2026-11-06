import Mathlib

theorem algebra_2612 : Real.sqrt (8 + Real.sqrt 63) + Real.sqrt (8 - Real.sqrt 63) = 3 * Real.sqrt 2 := by
  have h1 : Real.sqrt 63 = Real.sqrt (63 : ℝ) := by rfl
  have h2 : 0 ≤ Real.sqrt (8 + Real.sqrt 63) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (8 - Real.sqrt 63) := Real.sqrt_nonneg _
  have h4 : Real.sqrt (8 + Real.sqrt 63) ^ 2 = 8 + Real.sqrt 63 := by 
    rw [Real.sq_sqrt]
    positivity
  have h5 : Real.sqrt (8 - Real.sqrt 63) ^ 2 = 8 - Real.sqrt 63 := by 
    rw [Real.sq_sqrt]
    have h8 : Real.sqrt 63 ≤ (8 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (63 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (63 : ℝ) by positivity)]
    nlinarith
  have h6 : Real.sqrt (8 + Real.sqrt 63) * Real.sqrt (8 - Real.sqrt 63) = 1 := by
    have h7 : Real.sqrt (8 + Real.sqrt 63) * Real.sqrt (8 - Real.sqrt 63) = Real.sqrt ((8 + Real.sqrt 63) * (8 - Real.sqrt 63)) := by 
      rw [← Real.sqrt_mul (by
        nlinarith [Real.sqrt_nonneg (8 + Real.sqrt 63), Real.sqrt_nonneg (8 - Real.sqrt 63)]
      )]
    rw [h7]
    have h8 : (8 + Real.sqrt 63) * (8 - Real.sqrt 63) = (1 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (63 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (63 : ℝ) by positivity)]
    rw [h8]
    have h9 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by
      simp
    rw [h9]
  have h7 : (Real.sqrt (8 + Real.sqrt 63) + Real.sqrt (8 - Real.sqrt 63)) ^ 2 = 18 := by
    nlinarith [Real.sqrt_nonneg (8 + Real.sqrt 63), Real.sqrt_nonneg (8 - Real.sqrt 63), h4, h5, h6, Real.sqrt_nonneg (63 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (63 : ℝ) by positivity)]
  have h8 : 0 ≤ Real.sqrt (8 + Real.sqrt 63) + Real.sqrt (8 - Real.sqrt 63) := by
    positivity
  have h9 : 0 ≤ 3 * Real.sqrt 2 := by
    positivity
  have h10 : Real.sqrt (8 + Real.sqrt 63) + Real.sqrt (8 - Real.sqrt 63) = 3 * Real.sqrt 2 := by
    have h11 : (Real.sqrt (8 + Real.sqrt 63) + Real.sqrt (8 - Real.sqrt 63)) ^ 2 = (3 * Real.sqrt 2) ^ 2 := by
      rw [h7]
      have h12 : (3 * Real.sqrt 2) ^ 2 = 18 := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by positivity)]
      rw [h12]
    have h13 : 0 ≤ Real.sqrt (8 + Real.sqrt 63) + Real.sqrt (8 - Real.sqrt 63) := by
      positivity
    have h14 : 0 ≤ 3 * Real.sqrt 2 := by
      positivity
    nlinarith [Real.sqrt_nonneg (2: ℝ), sq_nonneg (Real.sqrt (8 + Real.sqrt 63) + Real.sqrt (8 - Real.sqrt 63) - (3 * Real.sqrt 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by positivity)]
  exact h10