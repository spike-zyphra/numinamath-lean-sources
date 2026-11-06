import Mathlib

theorem algebra_310365 (x : ℝ) :
    Real.sqrt (x^2 + 6 * x + 36) = Real.sqrt (x^2 - 14 * x + 76) + 8 ↔ x = 10 := by

  constructor
  · -- Assume the equation holds, prove x = 10
    intro h_eq
    have h1 : 0 ≤ (x ^ 2 + 6 * x + 36 : ℝ) := by
      nlinarith [sq_nonneg (x + 3)]
    have h2 : 0 ≤ (x ^ 2 - 14 * x + 76 : ℝ) := by
      nlinarith [sq_nonneg (x - 7)]
    have h3 : Real.sqrt (x^2 + 6 * x + 36) = Real.sqrt (x^2 - 14 * x + 76) + 8 := h_eq
    have h4 : (Real.sqrt (x^2 + 6 * x + 36)) ^ 2 = (Real.sqrt (x^2 - 14 * x + 76) + 8) ^ 2 := by
      rw [h3]
    have h5 : (Real.sqrt (x^2 + 6 * x + 36)) ^ 2 = x^2 + 6 * x + 36 := by
      rw [Real.sq_sqrt]
      linarith [h1]
    have h6 : (Real.sqrt (x^2 - 14 * x + 76)) ^ 2 = x^2 - 14 * x + 76 := by
      rw [Real.sq_sqrt]
      linarith [h2]
    have h7 : (Real.sqrt (x^2 - 14 * x + 76) + 8) ^ 2 = (Real.sqrt (x^2 - 14 * x + 76)) ^ 2 + 16 * Real.sqrt (x^2 - 14 * x + 76) + 64 := by
      ring
    rw [h5] at h4
    rw [h7] at h4
    rw [h6] at h4
    have h8 : Real.sqrt (x ^ 2 - 14 * x + 76) = (5 * x - 26) / 4 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 14 * x + 76), sq_nonneg (Real.sqrt (x ^ 2 - 14 * x + 76)), sq_nonneg (5 * x - 26)]
    have h9 : ((Real.sqrt (x^2 - 14 * x + 76)) ) ^ 2 = (( (5 * x - 26) / 4 ) ) ^ 2 := by
      rw [h8]
    have h10 : x ^ 2 - 4 * x - 60 = 0 := by
      nlinarith [h9, sq_nonneg (5 * x - 26), Real.sqrt_nonneg (x ^ 2 - 14 * x + 76), h6, Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 - 14 * x + 76 : ℝ) by linarith)]
    have h11 : (x - 10) * (x + 6) = 0 := by
      nlinarith [h10]
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- x - 10 = 0, so x = 10
      linarith
    · -- x + 6 = 0, so x = -6
      have h14 : x = -6 := by linarith
      rw [h14] at h_eq
      nlinarith [Real.sqrt_nonneg ( (-6 : ℝ) ^ 2 + 6 * (-6) + 36 ), Real.sqrt_nonneg ( (-6 : ℝ) ^ 2 - 14 * (-6) + 76 ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (-6 : ℝ) ^ 2 + 6 * (-6) + 36 by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (-6 : ℝ) ^ 2 - 14 * (-6) + 76 by nlinarith), 
          sq_nonneg (Real.sqrt ((-6 : ℝ) ^ 2 - 14 * (-6) + 76 ) - 6 ), 
          sq_nonneg (Real.sqrt ((-6 : ℝ) ^ 2 + 6 * (-6) + 36 ) - 14 )
        ]
  · -- Assume x = 10 prove the equation
    intro h_eq
    rw [show x = (10 : ℝ) by linarith]
    have h15 : Real.sqrt ((10 : ℝ) ^ 2 + 6 * (10 : ℝ) + 36) = 14 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h16 : Real.sqrt ((10 : ℝ) ^ 2 - 14 * (10 : ℝ) + 76) = 6 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h15, h16]
    all_goals norm_num