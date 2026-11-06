import Mathlib

theorem algebra_187803 (x : ℝ) (hx : 2 * x ^ 2 + 3 * x + 2 ≥ 0 ∧ 2 * x ^ 2 + 3 * x - 5 ≥ 0) :
    Real.sqrt (2 * x ^ 2 + 3 * x + 2) - Real.sqrt (2 * x ^ 2 + 3 * x - 5) = 1 ↔
    x = 2 ∨ x = -7 / 2 := by
  constructor
  · -- Assume Real.sqrt (2 * x ^ 2 + 3 * x + 2) - Real.sqrt (2 * x ^ 2 + 3 * x - 5) = 1, prove x = 2 ∨ x = -7 / 2
    intro h
    have h1 : Real.sqrt (2 * x ^ 2 + 3 * x + 2) = 1 + Real.sqrt (2 * x ^ 2 + 3 * x - 5) := by linarith
    have h2 : (Real.sqrt (2 * x ^ 2 + 3 * x + 2)) ^ 2 = (1 + Real.sqrt (2 * x ^ 2 + 3 * x - 5)) ^ 2 := by
      rw [h1]
    have h3 : (Real.sqrt (2 * x ^ 2 + 3 * x + 2)) ^ 2 = 2 * x ^ 2 + 3 * x + 2 := Real.sq_sqrt (show (2 * x ^ 2 + 3 * x + 2) ≥ 0 by linarith [hx.1])
    have h4 : (1 + Real.sqrt (2 * x ^ 2 + 3 * x - 5)) ^ 2 = 1 + 2 * Real.sqrt (2 * x ^ 2 + 3 * x - 5) + (Real.sqrt (2 * x ^ 2 + 3 * x - 5)) ^ 2 := by ring
    rw [h3, h4] at h2
    have h5 : (Real.sqrt (2 * x ^ 2 + 3 * x - 5)) ^ 2 = 2 * x ^ 2 + 3 * x - 5 := Real.sq_sqrt (show (2 * x ^ 2 + 3 * x - 5) ≥ 0 by linarith [hx.2])
    rw [h5] at h2
    have h6 : Real.sqrt (2 * x ^ 2 + 3 * x - 5) = 3 := by
      nlinarith
    have h7 : 2 * x ^ 2 + 3 * x - 5 = 9 := by
      calc
        2 * x ^ 2 + 3 * x - 5 = (Real.sqrt (2 * x ^ 2 + 3 * x - 5)) ^ 2 := by rw [Real.sq_sqrt (show (2 * x ^ 2 + 3 * x - 5) ≥ 0 by linarith [hx.2])]
        _ = 3 ^ 2 := by rw [h6]
        _ = (9 : ℝ) := by norm_num
    have h8 : 2 * x ^ 2 + 3 * x - 14 = 0 := by
      nlinarith
    have h9 : (x - 2) * (2 * x + 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- Case x - 2 = 0, so x = 2
      left
      linarith
    · -- Case 2x + 7 = 0, so x = -7/2
      right
      linarith
  · -- Assume x = 2 ∨ x = -7 / 2, prove Real.sqrt (2 * x ^ 2 + 3 * x + 2) - Real.sqrt (2 * x ^ 2 + 3 * x - 5) = 1
    rintro (h | h)
    · -- Case x = 2
      rw [h]
      have h1 : Real.sqrt (2 * (2: ℝ) ^ 2 + 3 * (2: ℝ) + 2) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (2 * (2: ℝ) ^ 2 + 3 * (2: ℝ) - 5) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num
    · -- Case x = -7/2
      rw [h]
      have h1 : Real.sqrt (2 * (-7 / 2 : ℝ) ^ 2 + 3 * (-7 / 2 : ℝ) + 2) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (2 * (-7 / 2 : ℝ) ^ 2 + 3 * (-7 / 2 : ℝ) - 5) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num