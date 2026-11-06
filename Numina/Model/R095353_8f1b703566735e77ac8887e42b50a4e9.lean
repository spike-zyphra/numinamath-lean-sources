import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_273664 {x : ℝ} (hx : x > 0) :
    x^2 + log x > x ↔ x ∈ Ioi 1 := by
  simp only [mem_Ioi]
  constructor
  · -- Forward: Assume x^2 + log x > x, prove x > 1
    intro h
    by_contra h2
    -- Assume for contradiction that x ≤ 1
    push_neg at h2
    -- Now we need to derive a contradiction
    have h3 : log x ≤ 0 := by
      have h4 : x ≤ 1 := h2
      have h5 : x > 0 := hx
      have h6 : log x ≤ log 1 := by
        apply Real.log_le_log
        all_goals nlinarith
      have h7 : log 1 = 0 := by
        simp [log_one]
      linarith
    -- Now, we need to show x^2 + log x - x ≤ 0
    have h4 : x^2 + log x - x ≤ 0 := by
      nlinarith [sq_nonneg (x - 1), Real.log_le_sub_one_of_pos hx, h3]
    linarith
  · -- Backward: Assume x > 1, prove x^2 + log x > x
    intro h
    have h2 : log x > 0 := by
      have h3 : x > 1 := h
      have h4 : x > 0 := by linarith
      have h5 : log x > log 1 := by
        apply Real.log_lt_log
        all_goals linarith
      have h6 : log 1 = 0 := by
        simp [log_one]
      linarith
    have h3 : x^2 + log x - x > 0 := by
      nlinarith [sq_nonneg (x - 1), sq_pos_of_pos (show (x - 1 : ℝ) > 0 by linarith [h]), Real.log_pos (show x > 1 by linarith [h]), h2, mul_self_nonneg (x - 1)]
    linarith