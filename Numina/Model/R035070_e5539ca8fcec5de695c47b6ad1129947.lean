import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_272102 {a : ℝ} (ha : a > 1) (f : ℝ → ℝ) (hf : f = λ x => a ^ x - x)
  (h3 : f 3 < 0) :
  1 < a ∧ a < 3 ^ ((1 : ℝ) / 3) := by 
  have h1 : a ^ (3 : ℝ) - 3 < 0 := by
    rw [hf] at h3
    simpa using h3
  have h2 : a ^ (3 : ℝ) < (3 : ℝ) := by linarith
  have h7 : a < (3 : ℝ) ^ ((1 : ℝ) / 3) := by
    by_contra h
    push_neg at h
    have h8 : a ^ (3 : ℝ) ≥ ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) := by
      apply Real.rpow_le_rpow
      all_goals 
        try nlinarith [show (3 : ℝ) ^ ((1 : ℝ) / 3) > 0 by positivity, Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (1 / 3)]
        try linarith
    have h9 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = (3 : ℝ) := by 
      rw [← Real.rpow_mul]
      norm_num 
      all_goals linarith
    have h10 : a ^ (3 : ℝ) ≥ (3 : ℝ) := by 
      calc 
        a ^ (3 : ℝ) ≥ ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) := h8
        _ = (3 : ℝ) := h9
    linarith
  constructor
  · linarith
  · linarith [h7]