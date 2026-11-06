import Mathlib

open Real

theorem algebra_185228 : 2019^(log (log 2019)) - (log 2019)^(log 2019) = 0 := by
  have h1 : (2019 : ℝ) ^ (log (log 2019)) = (log 2019) ^ (log 2019) := by 
    have h2 : log ((2019 : ℝ) ^ (log (log 2019))) = log ((log 2019) ^ (log 2019)) := by 
      have h3 : log ((2019 : ℝ) ^ (log (log 2019))) = log (log 2019) * log 2019 := by
        rw [log_rpow]
        all_goals
          have h3 : log 2019 > 0 := by
            apply log_pos
            norm_num
          nlinarith
      have h4 : log ((log 2019) ^ (log 2019)) = log 2019 * log (log 2019) := by 
        rw [log_rpow]
        all_goals 
          have h3 : log 2019 > 0 := by 
            apply log_pos
            norm_num
          nlinarith 
      linarith [h3, h4]
    have h6 : (2019 : ℝ) ^ (log (log 2019)) > 0 := by positivity
    have h7 : (log 2019) ^ (log 2019) > 0 := by positivity 
    have h8 : (2019 : ℝ) ^ (log (log 2019)) = (log 2019) ^ (log 2019) := by
      apply log_injOn_pos (Set.mem_Ioi.mpr h6) (Set.mem_Ioi.mpr h7) h2 
    exact h8 
  linarith [h1]