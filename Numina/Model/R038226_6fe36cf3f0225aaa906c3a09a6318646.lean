import Mathlib

open Real

theorem algebra_141232 (x : ℝ) :
    (5 : ℝ) ^ (x + 1) = (3 : ℝ) ^ (x ^ 2 - 1) ↔ x = -1 ∨ x = logb 3 5 + 1 := by
  constructor
  · -- Assume (5 : ℝ) ^ (x + 1) = (3 : ℝ) ^ (x ^ 2 - 1), prove x = -1 ∨ x = logb 3 5 + 1
    intro h_eq
    by_cases h1 : x = -1
    · -- x = -1
      left
      exact h1
    · -- x ≠ -1
      have h2 : x ≠ -1 := by
        intro h3
        apply h1
        exact h3
      have h3 : (5 : ℝ) ^ (x + 1) = (3 : ℝ) ^ (x ^ 2 - 1) := h_eq
      have h4 : (x + 1) * log (5 : ℝ) = (x ^ 2 - 1) * log (3 : ℝ) := by
        have h5 : log ((5 : ℝ) ^ (x + 1)) = log ((3 : ℝ) ^ (x ^ 2 - 1)) := by
          rw [h3]
        have h6 : log ((5 : ℝ) ^ (x + 1)) = (x + 1) * log (5 : ℝ) := by
          rw [log_rpow]
          all_goals norm_num
        have h7 : log ((3 : ℝ) ^ (x ^ 2 - 1)) = (x ^ 2 - 1) * log (3 : ℝ) := by
          rw [log_rpow]
          all_goals norm_num
        rw [h6, h7] at h5
        linarith
      have h6 : x ^ 2 * log (3 : ℝ) - x * log (5 : ℝ) - (log (5 : ℝ) + log (3 : ℝ)) = 0 := by
        nlinarith
      have h7 : (log (3 : ℝ)) ≠ 0 := by
        have h8 : (3 : ℝ) > 0 := by norm_num
        have h9 : (3 : ℝ) ≠ 1 := by norm_num
        exact log_ne_zero_of_pos_of_ne_one h8 h9
      have h9 : (x + 1) * (x - (logb 3 5 + 1)) = 0 := by
        have h7' : x ^ 2 * log (3 : ℝ) - x * log (5 : ℝ) - (log (5 : ℝ) + log (3 : ℝ)) = 0 := h6
        have h10 : log (5 : ℝ) = log (3 : ℝ) * (logb 3 5) := by
          field_simp [logb]
        rw [h10] at h7'
        have h12 : (x + 1) * (x - (logb 3 5 + 1)) = 0 := by
          nlinarith [ sq_pos_of_pos (show (3 : ℝ) > 0 by norm_num), sq_nonneg (x + 1), sq_nonneg (x - (logb 3 5 + 1)), Real.log_pos (show (3 : ℝ) > 1 by norm_num), Real.log_pos (show (5 : ℝ) > 1 by norm_num)]
        exact h12
      cases' (mul_eq_zero.mp h9) with h11 h12
      · -- h11 : x + 1 = 0
        exfalso
        apply h2
        have : x = -1 := by linarith
        tauto
      · -- h12 : x - (logb 3 5 + 1) = 0
        right
        linarith
  · -- Assume x = -1 ∨ x = logb 3 5 + 1, prove (5 : ℝ) ^ (x + 1) = (3 : ℝ) ^ (x ^ 2 - 1)
    rintro (h1 | h2)
    · -- h1 : x = -1
      rw [h1]
      norm_num
    · -- h2 : x = logb 3 5 + 1
      rw [h2]
      have h7 : ( (logb 3 5 + 1) + 1 ) * log (5 : ℝ) = ( (logb 3 5 + 1) ^ 2 - 1 ) * log (3 : ℝ) := by
        have h10 : logb 3 5 = (log (5 : ℝ)) / (log (3 : ℝ)) := by
          field_simp [logb]
        rw [h10]
        have h8 : log (3 : ℝ) ≠ 0 := by
          have h9 : (3 : ℝ) > 0 := by norm_num
          have h10 : (3 : ℝ) ≠ 1 := by norm_num
          exact log_ne_zero_of_pos_of_ne_one h9 h10
        field_simp [h8]
        nlinarith [ sq_pos_of_pos (show (3 : ℝ) > 0 by norm_num), sq_pos_of_pos (show (5 : ℝ) > 0 by norm_num), Real.log_pos (show (3 : ℝ) > 1 by norm_num), Real.log_pos (show (5 : ℝ) > 1 by norm_num) ]
      have h11 : log ((5 : ℝ) ^ ((logb 3 5 + 1) + 1)) = log ((3 : ℝ) ^ ((logb 3 5 + 1) ^ 2 - 1)) := by
        have h12 : log ((5 : ℝ) ^ ((logb 3 5 + 1) + 1)) = ( (logb 3 5 + 1) + 1 ) * log (5 : ℝ) := by
          rw [log_rpow]
          all_goals norm_num
        have h13 : log ((3 : ℝ) ^ ((logb 3 5 + 1) ^ 2 - 1)) = ( (logb 3 5 + 1) ^ 2 - 1 ) * log (3 : ℝ) := by
          rw [log_rpow]
          all_goals norm_num
        rw [h12, h13]
        linarith
      have h14 : (5 : ℝ)  ^ ((logb 3 5 + 1) + 1) = (3 : ℝ) ^ ((logb 3 5 + 1) ^ 2 - 1) := by
        exact log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h11
      exact h14