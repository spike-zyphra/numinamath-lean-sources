import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_171245 (x : ℝ) :
  x ∈ Ioo (-2) 13 ∧ logb 0.5 (sqrt (x + 3) - 1) / logb 0.5 (sqrt (x + 3) + 5) < 1 / 2 ↔
  x ∈ Ioo (-2) 13 := by
  constructor
  · -- Forward implication. Assume the inequality and x ∈ (-2, 13) holds, prove x ∈ (-2, 13)
    intro h
    exact h.1
  · -- Backward implication. Assume x ∈ (-2, 13) and prove the inequality holds
    intro h
    constructor
    · exact h
    · -- Now we need to prove that given x ∈ (-2, 13), the inequality holds.
      have h3 : -2 < x := h.left
      have h4 : x < 13 := h.right
      have h5 : x + 3 > 1 := by linarith
      have h6 : sqrt (x + 3) > 1 := by
        have h7 : sqrt (x + 3) > sqrt (1 : ℝ) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
        have h8 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
        linarith [h7, h8]
      have h9 : sqrt (x + 3) < 4 := by
        have h10 : sqrt (x + 3) < sqrt (16 : ℝ) := Real.sqrt_lt_sqrt (by linarith) (by linarith
          )
        have h11 : sqrt (16 : ℝ) = 4 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith [h10, h11]
      have h12 : sqrt (x + 3) - 1 > 0 := by
        linarith [h6]
      have h13 : sqrt (x + 3) + 5 > 0 := by
        nlinarith [Real.sqrt_nonneg (x + 3)]
      have h14 : logb 0.5 (sqrt (x + 3) - 1) / logb 0.5 (sqrt (x + 3) + 5) = (log (sqrt (x + 3) - 1) / log (sqrt (x + 3) + 5)) := by
        field_simp [logb]
        all_goals ring
      rw [h14]
      have h15 : log (sqrt (x + 3) + 5) > 0 := by
        have h16 : sqrt (x + 3) + 5 > 1 := by nlinarith [Real.sqrt_nonneg (x + 3), h3]
        have h17 : log (sqrt (x + 3) + 5) > log 1 := by
          apply Real.log_lt_log
          all_goals nlinarith [h13, h16]
        have h18 : log 1 = 0 := Real.log_one
        linarith [h17, h18]
      have h19 : log (sqrt (x + 3) - 1) < 1 / 2 * log (sqrt (x + 3) + 5) := by
        have h20 : (sqrt (x + 3) - 1) ^ 2 < sqrt (x + 3) + 5 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x + 3 by linarith), Real.sqrt_nonneg (x + 3), h3, h4, Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (x + 3) by linarith), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (16 : ℝ) by norm_num), sq_nonneg (sqrt (x + 3) - 4), sq_nonneg (sqrt (x + 3) - 1)]
        have h21 : log ((sqrt (x + 3) - 1) ^ 2) < log (sqrt (x + 3) + 5) := by
          apply Real.log_lt_log
          all_goals nlinarith [h20, h13, Real.sqrt_nonneg (x + 3), Real.sq_sqrt (show (0 : ℝ) ≤ x + 3 by linarith)]
        have h22 : log ((sqrt (x + 3) - 1) ^ 2) = 2 * log (sqrt (x + 3) - 1) := by
          rw [log_pow]
          simp
          all_goals linarith [h12]
        linarith [h22, h21]
      have h23 : log (sqrt (x + 3) - 1) / log (sqrt (x + 3) + 5) < 1 / 2 := by
        apply (div_lt_iff₀ (by linarith [h15])).mpr
        linarith [h19]
      linarith [h23]