import Mathlib

open Real Set

theorem inequalities_217947 (x : ℝ) :
    sqrt (7 + x) > 5 - x ↔ x > 2 := by
  constructor
  · -- Assume sqrt (7 + x) > 5 - x, prove x > 2
    intro h
    by_contra h1
    push_neg at h1
    by_cases h3 : x ≥ -7
    · -- Assume x ≥ -7
      have h4 : 7 + x ≥ 0 := by linarith
      have h5 : sqrt (7 + x) ≤ 5 - x := by
        have h4 : 7 + x ≥ 0 := by linarith
        have h6 : sqrt (7 + x) ^ 2 = 7 + x := by
          rw [Real.sq_sqrt]
          nlinarith
        nlinarith [sq_nonneg (sqrt (7 + x) - (5 - x)), sq_nonneg (x - 2), Real.sqrt_nonneg (7 + x), sq_nonneg (x), Real.sqrt_nonneg (7 + x)]
      linarith [h5, h]
    · -- Assume x < -7
      have h4 : x < -7 := by linarith
      have h5 : 7 + x < 0 := by linarith
      have h6 : sqrt (7 + x) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      rw [h6] at h
      nlinarith
  · -- Assume x > 2, prove sqrt (7 + x) > 5 - x
    intro h
    have h1 : x > 2 := h
    by_cases h2 : x < 5
    · -- Assume x < 5
      have h3 : x > 2 := by linarith
      have h4 : 7 + x > 0 := by linarith
      have h5 : 5 - x > 0 := by nlinarith
      have h6 : sqrt (7 + x) ^ 2 = 7 + x := by
        rw [Real.sq_sqrt]
        nlinarith
      have h7 : 7 + x > (5 - x) ^ 2 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 5), sq_nonneg (x - 4)]
      have h8 : sqrt (7 + x) > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith
      nlinarith [Real.sqrt_nonneg (7 + x), sq_nonneg (sqrt (7 + x) - (5 - x)), h6, sq_nonneg (x - 2)]
    · -- Assume x ≥ 5
      have h4 : x ≥ 5 := by linarith
      have h5 : 5 - x ≤ 0 := by linarith
      have h4' : 7 + x ≥ 0 := by linarith
      have h7 : sqrt (7 + x) ≥ 0 := Real.sqrt_nonneg (7 + x)
      by_cases h7' : 7 + x > 0
      · -- Assume 7 + x > 0
        have h8 : sqrt (7 + x) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        nlinarith [Real.sqrt_nonneg (7 + x)]
      · -- Assume 7 + x = 0
        nlinarith