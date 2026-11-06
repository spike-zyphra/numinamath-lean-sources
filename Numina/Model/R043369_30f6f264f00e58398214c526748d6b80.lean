import Mathlib

theorem algebra_20501 (x : ℝ) (hx : x ≤ 11 / 2) :
    x = Real.sqrt (11 - 2 * x) + 4 ↔ x = 5 := by
  constructor
  · -- Assume x = Real.sqrt (11 - 2 * x) + 4, prove x = 5
    intro h
    have h1 : Real.sqrt (11 - 2 * x) = x - 4 := by
      linarith
    have h2 : 0 ≤ Real.sqrt (11 - 2 * x) := Real.sqrt_nonneg (11 - 2 * x)
    have h3 : 0 ≤ x - 4 := by
      linarith [h1, h2]
    have h4 : (Real.sqrt (11 - 2 * x)) ^ 2 = (x - 4) ^ 2 := by
      rw [h1]
    have h5 : (Real.sqrt (11 - 2 * x)) ^ 2 = 11 - 2 * x := by 
      rw [Real.sq_sqrt]
      nlinarith
    have h6 : 11 - 2 * x = (x - 4) ^ 2 := by
      linarith [h5, h4]
    have h7 : x ^ 2 - 6 * x + 5 = 0 := by
      nlinarith
    have h8 : (x - 5) * (x - 1) = 0 := by 
      nlinarith [h7]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case where x - 5 = 0, so x = 5
      linarith
    · -- Case where x - 1 = 0, so x = 1
      have h8 : x = 1 := by linarith
      rw [h8] at h3
      nlinarith
  · -- Now prove reverse direction
    intro h
    rw [h]
    have h4 : Real.sqrt (11 - 2 * (5 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h4]
    all_goals norm_num