import Mathlib

open Real

theorem inequalities_304505 (x : ℝ) (hx : 0 ≤ x + 1) :
    x + sqrt (x + 1) > 11 / 4 ↔ x > 5 / 4 := by
  constructor
  · -- Forward direction: If x + sqrt(x + 1) > 11/4, then x > 5/4
    intro h
    by_contra h'
    push_neg at h'
    have h1 : sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
    have h2 : x ≤ 5 / 4 := by linarith
    have h3 : sqrt (x + 1) ≤ 3 / 2 := by
      nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith), h2]
    nlinarith [h1, h3]
  · -- Reverse direction: If x > 5/4, then x + sqrt(x + 1) > 11/4
    intro h
    have h1 : sqrt (x + 1) > 3 / 2 := by
      have h4 : x + 1 > (3 / 2) ^ 2 := by
        nlinarith
      have h5 : sqrt (x + 1) > 3 / 2 := by
        have h6 : (3 / 2 : ℝ) ^ 2 < x + 1 := by linarith
        have h7 : (3 / 2 : ℝ) < sqrt (x + 1) := by
          apply Real.lt_sqrt_of_sq_lt
          all_goals linarith
        linarith
      linarith
    nlinarith [h1, h]