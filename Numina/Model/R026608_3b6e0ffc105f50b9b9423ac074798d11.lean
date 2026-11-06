import Mathlib

theorem algebra_314079 (x : ℝ) :
    Real.sqrt (x^2 - x - 2) + Real.sqrt (x^2 - 3 * x + 5) = 3 ↔
    x = -1 ∨ x = 2 + 3 / 8 := by
  constructor
  · -- Assume sqrt(x^2 - x - 2) + sqrt(x^2 - 3 * x + 5) = 3, prove x = -1 ∨ x = 2 + 3/8
    intro h
    have h1 : 0 ≤ x^2 - x - 2 := by
      by_contra h1
      push_neg at h1
      have h11 : Real.sqrt (x^2 - x - 2) = 0 := by 
        rw [Real.sqrt_eq_zero']
        nlinarith
      rw [h11] at h
      have h2 : Real.sqrt (x^2 - 3 * x + 5) = 3 := by linarith
      have h12 : x^2 - 3 * x + 5 < (9 : ℝ) := by 
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x - 3/2)]
      have h13 : Real.sqrt (x^2 - 3 * x + 5) < (3 : ℝ) := by 
        have h14 : Real.sqrt (x^2 - 3 * x + 5) < Real.sqrt (9 : ℝ) := by
          apply Real.sqrt_lt_sqrt
          · nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1)]
          · nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x - 3/2)]
        have h15 : Real.sqrt (9 : ℝ) = (3 : ℝ) := by 
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        linarith [h14, h15]
      linarith
    have h11 : 0 ≤ x^2 - 3 * x + 5 := by
      nlinarith [sq_nonneg (x - 3 / 2)]
    have h10 : Real.sqrt (x^2 - x - 2) ≥ 0 := Real.sqrt_nonneg (x^2 - x - 2)
    have h111 : Real.sqrt (x^2 - 3 * x + 5) ≥ 0 := Real.sqrt_nonneg (x^2 - 3 * x + 5)
    have h6 : Real.sqrt (x^2 - x - 2) = 3 - Real.sqrt (x^2 - 3 * x + 5) := by linarith
    have h7 : (Real.sqrt (x^2 - x - 2)) ^ 2 = (3 - Real.sqrt (x^2 - 3 * x + 5)) ^ 2 := by
      rw [h6]
    have h8 : (Real.sqrt (x^2 - x - 2)) ^ 2 = x^2 - x - 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h1111 : (Real.sqrt (x^2 - 3 * x + 5)) ^ 2 = x^2 - 3 * x + 5 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h9 : (3 - Real.sqrt (x^2 - 3 * x + 5)) ^ 2 = 9 - 6 * Real.sqrt (x^2 - 3 * x + 5) + (Real.sqrt (x^2 - 3 * x + 5) ^ 2) := by
      ring
    rw [h9] at h7
    rw [h8] at h7
    rw [h1111] at h7
    have h10 : Real.sqrt (x^2 - 3 * x + 5) = (8 - x) / 3 := by
      nlinarith [Real.sqrt_nonneg (x^2 - 3 * x + 5)]
    have h33 : (Real.sqrt (x^2 - 3 * x + 5)) ^ 2 = ((8 - x) / 3) ^ 2 := by
      rw [h10]
    have h34 : 8 * x ^ 2 - 11 * x - 19 = 0 := by
      nlinarith [h33, h1111]
    have h35 : (x + 1) * (8 * x - 19) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h35) with h36 h37
    · -- x + 1 = 0
      left
      linarith
    · -- 8x - 19 = 0
      right
      linarith
  · -- Assume x = -1 ∨ x = 2 + 3/8, prove sqrt(x^2 - x - 2) + sqrt(x^2 - 3 * x + 5) = 3
    rintro (h | h)
    · -- x = -1
      rw [show x = -1 by linarith]
      have h1 : Real.sqrt ((-1 : ℝ)^2 - (-1 : ℝ) - 2) = (0 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      have h2 : Real.sqrt ((-1 : ℝ)^2 - 3 * (-1 : ℝ) + 5) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num
    · -- x = 2 + 3/8 = 19/8
      have h7 : x = (19 / 8 : ℝ) := by
        linarith
      rw [h7]
      have h100 : Real.sqrt ((19 / 8 : ℝ)^2 - (19 / 8 : ℝ) - 2) = (9 / 8 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      have h101 : Real.sqrt ((19 / 8 : ℝ)^2 - 3 * (19 / 8 : ℝ) + 5) = (15 / 8 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h100, h101]
      norm_num