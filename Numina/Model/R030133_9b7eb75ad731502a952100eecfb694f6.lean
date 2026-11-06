import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_103557 {x : ℝ} (hx : 0 < x) (h : log x ≥ log 2 + (1 / 2) * log x) :
    x ≥ 4 := by
  have h1 : (1 / 2) * log x ≥ log 2 := by 
    linarith
  have h2 : log x ≥ 2 * log 2 := by
    linarith [h1]
  have h3 : 2 * log 2 = log (2 ^ 2) := by
    simp [log_pow]
  have h4 : 2 * log 2 = log 4 := by
    rw [h3]
    all_goals norm_num
  have h5 : log x ≥ log 4 := by
    linarith [h2, h4]
  by_contra h7
  push_neg at h7
  have h7' : x < 4 := h7
  have h8 : log x < log 4 := by
    apply Real.log_lt_log
    all_goals linarith
  linarith [h5, h8]