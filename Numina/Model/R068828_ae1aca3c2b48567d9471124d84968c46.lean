import Mathlib

theorem algebra_139304 (x : ℝ) (hx : x ≥ 7) :
    Real.sqrt (x - 2) + Real.sqrt (x - 7) = 5 ↔ x = 11 := by
  constructor
  · -- Forward implication: if $\sqrt{x-2} + \sqrt{x-7} = 5$, then $x = 11$
    intro h
    have h1 : Real.sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
    have h2 : Real.sqrt (x - 7) ≥ 0 := Real.sqrt_nonneg (x - 7)
    have h3 : Real.sqrt (x - 2) + Real.sqrt (x - 7) = 5 := h
    have h4 : Real.sqrt (x - 2) = 3 := by
      nlinarith [Real.sq_sqrt (show (x - 2) ≥ 0 by linarith), Real.sq_sqrt (show (x - 7) ≥ 0 by linarith),
        h1, h2, h3]
    have h5 : (Real.sqrt (x - 2)) ^ 2 = 9 := by
      rw [h4]
      norm_num
    have h6 : (Real.sqrt (x - 2)) ^ 2 = x - 2 := by
      rw [Real.sq_sqrt]
      linarith
    linarith 
  · -- Backward direction: if x = 11, then $\sqrt{x-2} + \sqrt{x-7} = 5$
    intro h
    rw [h]
    have h1 : Real.sqrt (11 - 2 : ℝ) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (11 - 7 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num