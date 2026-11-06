import Mathlib


theorem algebra_132007 : (1005 : ℝ) ^ Real.log 121 = (11 : ℝ) ^ Real.log (∑ i in Finset.range 1005, (2 * i + 1)) := by
  have h1 : Real.log 121 = 2 * Real.log 11 := by
    calc
      Real.log 121 = Real.log ((11 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log (11 : ℝ) := by simp [Real.log_pow]
  have h3 : (∑ i in Finset.range 1005, (2 * i + 1 : ℝ)) = (1005 : ℝ) ^ 2 := by
    norm_num [Finset.sum_range_succ]
  have h4 : Real.log (∑ i in Finset.range 1005, (2 * i + 1 : ℝ)) = 2 * Real.log (1005 : ℝ) := by
    rw [h3]
    have h5 : Real.log ((1005 : ℝ) ^ 2) = 2 * Real.log (1005 : ℝ) := by
      simp [Real.log_pow]
    linarith
  rw [h1, h4]
  have h7 : (1005 : ℝ) ^ (2 * Real.log 11) = (11 : ℝ) ^ (2 * Real.log 1005) := by
    have h6 : (1005 : ℝ) ^ Real.log 11 = (11 : ℝ) ^ Real.log 1005 := by
      have h7 : Real.log ((1005 : ℝ) ^ Real.log 11) = Real.log ((11 : ℝ) ^ Real.log 1005) := by
        rw [Real.log_rpow, Real.log_rpow]
        all_goals
          try linarith
      have h8 : (1005 : ℝ) ^ Real.log 11 > 0 := by positivity
      have h9 : (11 : ℝ) ^ Real.log 1005 > 0 := by positivity
      have h10 : (1005 : ℝ) ^ Real.log 11 = (11 : ℝ) ^ Real.log 1005 := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr h8) (Set.mem_Ioi.mpr h9) h7
      exact h10
    calc
      (1005 : ℝ) ^ (2 * Real.log 11) = ((1005 : ℝ) ^ Real.log 11) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals
          positivity
      _ = ((11 : ℝ) ^ Real.log 1005) ^ 2 := by
        rw [show (1005 : ℝ) ^ Real.log 11 = (11 : ℝ) ^ Real.log 1005 by linarith [h6]]
      _ = (11 : ℝ) ^ (2 * Real.log 1005) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals
          positivity
  linarith