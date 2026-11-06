import Mathlib

theorem algebra_134253 (x : ℝ) (hx : x^2 - 1 / 5 ≥ 0) :
    5 * x^2 + x - x * Real.sqrt (5 * x^2 - 1) - 2 = 0 ↔
    x = Real.sqrt 10 / 5 ∨ x = -Real.sqrt 10 / 5 := by
  constructor
  · -- Assume the equation equals zero
    intro h
    have h1 : Real.sqrt (5 * x^2 - 1) ≥ 0 := by positivity
    have h2 : 5 * x^2 - 1 ≥ 0 := by
      nlinarith [hx]
    have h3 : 5 * x^2 + x - 2 = x * Real.sqrt (5 * x^2 - 1) := by linarith
    -- Square both sides to remove the square root
    have h4 : (5 * x^2 + x - 2)^2 = (x * Real.sqrt (5 * x^2 - 1))^2 := by
      rw [h3]
    have h5 : (x * Real.sqrt (5 * x^2 - 1))^2 = x^2 * (Real.sqrt (5 * x^2 - 1))^2 := by
      ring
    have h6 : (Real.sqrt (5 * x^2 - 1))^2 = 5 * x^2 - 1 := by
      rw [Real.sq_sqrt]
      nlinarith
    rw [h5, h6] at h4
    have h7 : (5 * x^2 + x - 2)^2 - x^2 * (5 * x^2 - 1) = 0 := by
      nlinarith [h4]
    have h8 : (x - Real.sqrt 10 / 5) * (x + Real.sqrt 10 / 5) = 0 := by
      nlinarith [sq_nonneg (x^2 * 5 -2), sq_nonneg (x * Real.sqrt 10), Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), sq_nonneg (x - Real.sqrt 10 / 5), sq_nonneg (x + Real.sqrt 10 / 5), sq_nonneg (5 * x^2 -1)]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case x - Real.sqrt 10 / 5 = 0
      left
      linarith
    · -- Case x + Real.sqrt 10 / 5 = 0
      right
      linarith
  · -- Prove the converse
    rintro (h | h)
    · -- Case x = Real.sqrt 10 / 5
      rw [h]
      have h1 : Real.sqrt (5 * (Real.sqrt 10 / 5) ^ 2 - 1) = 1 := by
        have h3 : 5 * (Real.sqrt 10 / 5) ^ 2 - 1 = (1 : ℝ) := by
          have h4 : (Real.sqrt 10 / 5) ^ 2 = (10 / 25 : ℝ) := by
            calc
              (Real.sqrt 10 / 5) ^ 2 = ((Real.sqrt 10)) ^ 2 / (5 : ℝ) ^ 2 := by field_simp
              _ = ((Real.sqrt 10)) ^ 2 / (25 : ℝ) := by norm_num
              _ = (10 / 25 : ℝ) := by
                have h5 : (Real.sqrt 10 : ℝ) ^ 2 = (10 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
                rw [h5]
          nlinarith
        rw [h3]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h1, Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    · -- Case x = -Real.sqrt 10 / 5
      rw [h]
      have h1 : Real.sqrt (5 * (-Real.sqrt 10 / 5) ^ 2 - 1) = 1 := by
        have h3 : 5 * (-Real.sqrt 10 / 5) ^ 2 - 1 = (1 : ℝ) := by
          have h4 : (-Real.sqrt 10 / 5) ^ 2 = (10 / 25 : ℝ) := by
            calc
              (-Real.sqrt 10 / 5) ^ 2 = ((-Real.sqrt 10)) ^ 2 / (5 : ℝ) ^ 2 := by field_simp
              _ = ((Real.sqrt 10)) ^ 2 / (25 : ℝ) := by ring_nf
              _ = (10 / 25 : ℝ) := by
                have h5 : (Real.sqrt 10 : ℝ) ^ 2 = (10 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
                rw [h5]
                <;> norm_num
          nlinarith
        rw [h3]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h1, Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]