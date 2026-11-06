import Mathlib

open Real

theorem algebra_255250 : (2021 : ℝ) ^ sqrt (logb 2021 2022) = 2022 ^ sqrt (logb 2022 2021) := by 
  have h1 : logb 2021 2022 = log 2022 / log 2021 := by 
    field_simp [logb]
  have h2 : logb 2022 2021 = log 2021 / log 2022 := by
    field_simp [logb]
  rw [h1, h2]
  have h3 : (2021 : ℝ) ^ sqrt (log 2022 / log 2021) = (2022 : ℝ) ^ sqrt (log 2021 / log 2022) := by
    have h4 : sqrt (log 2022 / log 2021) * log 2021 = sqrt (log 2021 / log 2022) * log 2022 := by
      have h5 : (sqrt (log 2022 / log 2021) * log 2021) ^ 2 = (sqrt (log 2021 / log 2022) * log 2022) ^ 2 := by
        have h6 : (sqrt (log 2022 / log 2021) * log 2021) ^ 2 = log 2022 * log 2021 := by
          calc
            (sqrt (log 2022 / log 2021) * log 2021) ^ 2
              = (sqrt (log 2022 / log 2021)) ^ 2 * (log 2021) ^ 2 := by ring
            _ = (log 2022 / log 2021) * (log 2021) ^ 2 := by
              rw [Real.sq_sqrt]
              positivity
            _ = log 2022 * log 2021 := by 
              field_simp
              <;> ring 
        have h7 : (sqrt (log 2021 / log 2022) * log 2022) ^ 2 = log 2021 * log 2022 := by
          calc
            (sqrt (log 2021 / log 2022) * log 2022) ^ 2
              = (sqrt (log 2021 / log 2022)) ^ 2 * (log 2022) ^ 2 := by ring
            _ = (log 2021 / log 2022) * (log 2022) ^ 2 := by 
              rw [Real.sq_sqrt]
              positivity 
            _ = log 2021 * log 2022 := by
              field_simp
              <;> ring 
        rw [h6, h7]
        <;> ring
      have h8 : 0 ≤ sqrt (log 2022 / log 2021) * log 2021 := by 
        have h9 : log 2021 > 0 := by
          apply log_pos 
          all_goals norm_num 
        have h10 : sqrt (log 2022 / log 2021) ≥ 0 := by apply Real.sqrt_nonneg 
        nlinarith 
      have h10 : 0 ≤ sqrt (log 2021 / log 2022) * log 2022 := by 
        have h11 : log 2022 > 0 := by
          apply log_pos 
          all_goals norm_num 
        have h12 : sqrt (log 2021 / log 2022) ≥ 0 := by apply Real.sqrt_nonneg 
        nlinarith 
      nlinarith 
    have h5' : log ((2021 : ℝ) ^ sqrt (log 2022 / log 2021)) = log ((2022 : ℝ) ^ sqrt (log 2021 / log 2022)) := by
      have h5 : sqrt (log 2022 / log 2021) * log 2021 = sqrt (log 2021 / log 2022) * log 2022 := h4
      have h5' : log ((2021 : ℝ) ^ sqrt (log 2022 / log 2021)) = sqrt (log 2022 / log 2021) * log 2021 := by
        rw [log_rpow]
        all_goals linarith 
      have h5'' : log ((2022 : ℝ) ^ sqrt (log 2021 / log 2022)) = sqrt (log 2021 / log 2022) * log 2022 := by
        rw [log_rpow]
        all_goals linarith 
      rw [h5', h5'', h4]
      <;> linarith 
    have h9 : (2021 : ℝ) ^ sqrt (log 2022 / log 2021) > 0 := by positivity 
    have h10 : (2022 : ℝ) ^ sqrt (log 2021 / log 2022) > 0 := by positivity 
    have h11 : (2021 : ℝ) ^ sqrt (log 2022 / log 2021) = (2022 : ℝ) ^ sqrt (log 2021 / log 2022) := by 
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h9) (Set.mem_Ioi.mpr h10) h5' 
    exact h11
  exact h3