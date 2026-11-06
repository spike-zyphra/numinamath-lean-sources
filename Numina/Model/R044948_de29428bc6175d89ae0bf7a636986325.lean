import Mathlib

theorem algebra_251991 (x : ℝ) (hx : 2 ≤ x) : 3 * Real.sqrt (x + 3) - Real.sqrt (x - 2) = 7 ↔ x = 6 := by
  constructor
  · -- Assume 3 * sqrt(x + 3) - sqrt(x - 2) = 7, prove x = 6
    intro h
    have h1 : 2 ≤ x := hx
    have h2 : 3 * Real.sqrt (x + 3) = 7 + Real.sqrt (x - 2) := by linarith
    have h3 : Real.sqrt (x + 3) ≥ 0 := Real.sqrt_nonneg (x + 3)
    have h4 : Real.sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
    have h5 : (3 * Real.sqrt (x + 3)) ^ 2 = (7 + Real.sqrt (x - 2)) ^ 2 := by
      rw [show 3 * Real.sqrt (x + 3) = 7 + Real.sqrt (x - 2) by linarith [h2]]
    have h6 : (3 * Real.sqrt (x + 3)) ^ 2 = 9 * (x + 3) := by
      calc
        (3 * Real.sqrt (x + 3)) ^ 2 = 9 * (Real.sqrt (x + 3) ^ 2) := by ring
        _ = 9 * (x + 3) := by
          rw [Real.sq_sqrt]
          linarith
    have h7 : (7 + Real.sqrt (x - 2)) ^ 2 = 49 + 14 * Real.sqrt (x - 2) + (x - 2) := by
      nlinarith [Real.sq_sqrt (show (x - 2 : ℝ) ≥ 0 by linarith)]
    rw [h6, h7] at h5
    have h8 : 8 * x - 20 = 14 * Real.sqrt (x - 2) := by
      nlinarith [h5]
    have h9 : 4 * x - 10 = 7 * Real.sqrt (x - 2) := by
      linarith [h8]
    have h10 : (4 * x - 10) ^ 2 = (7 * Real.sqrt (x - 2)) ^ 2 := by
      rw [show 4 * x - 10 = 7 * Real.sqrt (x - 2) by linarith [h9]]
    have h11 : (7 * Real.sqrt (x - 2)) ^ 2 = 49 * (x - 2) := by
      calc
        (7 * Real.sqrt (x - 2)) ^ 2 = 49 * (Real.sqrt (x - 2) ^ 2) := by ring
        _ = 49 * (x - 2) := by
          rw [Real.sq_sqrt]
          linarith
    have h12 : (4 * x - 10) ^ 2 = 49 * (x - 2) := by
      linarith [h10, h11]
    have h13 : (x - 6) * (x - 33 / 16) = 0 := by 
      nlinarith [h12]
    cases' (mul_eq_zero.1 h13) with h14 h15
    · -- Case x - 6 = 0, so x = 6
      linarith
    · -- Case x - 33/16 = 0, so x = 33/16
      have h16 : x = (33 / 16 : ℝ) := by linarith
      nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 2), 
                Real.sq_sqrt (show (x + 3 : ℝ) ≥ 0 by nlinarith), 
                Real.sq_sqrt (show (x - 2 : ℝ) ≥ 0 by nlinarith),
                h16, h1]
  · -- Assume x = 6, prove 3 * sqrt(x + 3) - sqrt(x - 2) = 7
    intro h
    rw [show x = (6 : ℝ) by linarith [h]]
    have h17 : Real.sqrt (6 + 3) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h18 : Real.sqrt (6 - 2) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h17, h18]
    all_goals norm_num