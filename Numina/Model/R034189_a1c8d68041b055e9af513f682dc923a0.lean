import Mathlib

theorem algebra_324737 (x : ℝ) (hx : x ≥ 1) :
    2 * (x + Real.sqrt (x ^ 2 - 1)) = (x - 1 + Real.sqrt (x + 1)) ^ 2 ↔ x = 1 ∨ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 1 or x = 2
    intro h_eq
    have h1 : x ^ 2 - 1 ≥ 0 := by nlinarith
    have h2 : x + 1 ≥ 0 := by nlinarith
    have h5 : (x - 1) ≥ 0 := by linarith
    have h6 : (x + 1) ≥ 0 := by linarith
    have h_eq2 : (x - 1) * (x - 2) = 0 := by
      have h9 : 2 * (x + Real.sqrt (x ^ 2 - 1)) = (x - 1 + Real.sqrt (x + 1)) ^ 2 := by 
        linarith [h_eq]
      have h10 : (x - 1 + Real.sqrt (x + 1)) ^ 2 = (x - 1) ^ 2 + 2 * (x - 1) * Real.sqrt (x + 1) + (Real.sqrt (x + 1)) ^ 2 := by 
        ring
      rw [h10] at h9
      have h11 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := by
        rw [Real.sq_sqrt]
        nlinarith
      rw [h11] at h9
      have h13 : Real.sqrt (x ^ 2 - 1) = Real.sqrt (x - 1) * Real.sqrt (x + 1) := by
        have h100 : (x ^ 2 - 1 : ℝ) = (x - 1) * (x + 1) := by nlinarith
        have h110 : Real.sqrt (x ^ 2 - 1) = Real.sqrt ((x - 1) * (x + 1)) := by
          rw [show (x ^ 2 - 1) = (x - 1) * (x + 1) by linarith [h100]]
        rw [h110]
        have h15 : Real.sqrt ((x - 1) * (x + 1)) = Real.sqrt (x - 1) * Real.sqrt (x + 1) := by
          rw [Real.sqrt_mul (by nlinarith)]
        linarith [h15, h110]
      rw [h13] at h9
      have h14 : (x - 1) * (x - 2) = 0 := by
        nlinarith [sq_nonneg (Real.sqrt (x - 1) - 1), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt 3), 
              sq_nonneg (x - 2), sq_nonneg (x - 1), 
              Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x + 1), 
              Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by nlinarith), 
              Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by nlinarith), 
              sq_nonneg (Real.sqrt (x - 1) - Real.sqrt (x + 1)), 
              mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (x + 1)), 
              mul_nonneg (show 0 ≤ x - 1 by nlinarith) (show 0 ≤ x + 1 by nlinarith)]
      linarith
    cases' (mul_eq_zero.1 h_eq2) with h9 h10
    · -- x - 1 = 0
      left
      linarith
    · -- x - 2 = 0
      right
      linarith
  · -- Assume x = 1 or x = 2, prove the equation
    rintro (h | h)
    · -- x = 1
      rw [show x = (1 : ℝ) by linarith [h]]
      have h1 : Real.sqrt ((1 : ℝ) ^ 2 - 1) = 0 := by
        rw [show (1 : ℝ) ^ 2 - 1 = (0 : ℝ) by norm_num]
        simp
      have h2 : Real.sqrt ((1 : ℝ) + 1) = Real.sqrt 2 := by
        norm_num
      rw [h1, h2]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- x = 2
      rw [show x = (2 : ℝ) by linarith [h]]
      have h1 : Real.sqrt ((2 : ℝ) ^ 2 - 1) = Real.sqrt 3 := by
        norm_num
      have h2 : Real.sqrt ((2 : ℝ) + 1) = Real.sqrt 3 := by
        norm_num
      rw [h1, h2]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]