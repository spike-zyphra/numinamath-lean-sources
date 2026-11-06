import Mathlib

theorem algebra_252483 (x : ℝ) (hx : 4 - 6 * x - x ^ 2 ≥ 0) :
    Real.sqrt (4 - 6 * x - x ^ 2) = x + 4 ↔ x = -1 := by
  constructor
  · -- Assume $\sqrt{4 - 6x - x^2} = x + 4$ prove $x = -1$
    intro h
    have h1 : (Real.sqrt (4 - 6 * x - x ^ 2)) ^ 2 = (x + 4) ^ 2 := by
      rw [h]
    have h2 : (Real.sqrt (4 - 6 * x - x ^ 2)) ^ 2 = 4 - 6 * x - x ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h2] at h1
    have h4 : x ^ 2 + 7 * x + 6 = 0 := by
      nlinarith
    have h5 : (x + 1) * (x + 6) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case where x + 1 = 0, so x = -1
      linarith
    · -- Case where x + 6 = 0, so x = -6, which is extraneous
      have h8 : x = -6 := by linarith
      rw [h8] at h
      have h9 : Real.sqrt (4 - 6 * (-6 : ℝ) - (-6 : ℝ) ^ 2) = ( (-6 : ℝ) + 4 ) := by
        linarith [h]
      have h10 : Real.sqrt (4 - 6 * (-6 : ℝ) - (-6 : ℝ) ^ 2) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h10] at h9
      norm_num at h9
      all_goals nlinarith
  · -- Assume x = -1 prove $\sqrt{4 - 6x - x^2} = x + 4$
    intro h
    rw [h]
    have h8 : Real.sqrt (4 - 6 * (-1 : ℝ) - (-1 : ℝ) ^ 2) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h8]
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num