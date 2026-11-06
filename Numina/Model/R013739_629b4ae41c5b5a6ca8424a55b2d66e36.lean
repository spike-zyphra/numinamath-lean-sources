import Mathlib

theorem algebra_254558 : 2017 ^ Real.log (Real.log 2017) - (Real.log 2017) ^ (Real.log 2017) = 0 := by
  have h1 : (2017 : ℝ) ^ Real.log (Real.log 2017) = (Real.log 2017) ^ (Real.log 2017) := by
    have h2 : Real.log ((2017 : ℝ) ^ Real.log (Real.log 2017)) = Real.log ((Real.log 2017) ^ (Real.log 2017)) := by
      have h3 : Real.log ((2017 : ℝ) ^ (Real.log (Real.log 2017) : ℝ)) = Real.log (Real.log 2017 : ℝ) * Real.log (2017 : ℝ) := by
        rw [Real.log_rpow]
        all_goals linarith
      have h4 : Real.log ((Real.log 2017 : ℝ) ^ (Real.log 2017 : ℝ)) = Real.log 2017 * Real.log (Real.log 2017 : ℝ) := by
        rw [Real.log_rpow]
        all_goals
          have h7 : (Real.log 2017 : ℝ) > 0 := by
            have h8 : (2017 : ℝ) > 1 := by norm_num
            have h9 : (Real.log 2017 : ℝ) > (Real.log 1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h10 : (Real.log 1 : ℝ) = 0 := Real.log_one
            linarith
          nlinarith
      rw [h3, h4]
      <;> nlinarith [Real.log_pos (show (2017 : ℝ) > 1 by norm_num)]
    have h3 : (2017 : ℝ) ^ Real.log (Real.log 2017 : ℝ) > 0 := by positivity
    have h4 : (Real.log 2017 : ℝ) ^ (Real.log 2017 : ℝ) > 0 := by positivity
    have h7 : (2017 : ℝ) ^ Real.log (Real.log 2017) = (Real.log 2017) ^ (Real.log 2017) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h3) (Set.mem_Ioi.mpr h4) h2
    exact h7
  linarith [h1]