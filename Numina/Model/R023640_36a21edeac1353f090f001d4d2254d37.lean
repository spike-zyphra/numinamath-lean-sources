import Mathlib

open Real

theorem algebra_189503 : logb (Real.sqrt 3 / 3) (logb 8 (Real.sqrt 2 / 2) - logb 3 (Real.sqrt 3 / 3)) = 2 := by
  have h1 : logb 8 (Real.sqrt 2 / 2) = -1 / 6 := by
    have h2 : logb 8 (Real.sqrt 2 / 2) = (log (Real.sqrt 2 / 2)) / (log (8 : ℝ)) := by 
      field_simp [logb]
    rw [h2]
    have h3 : log (Real.sqrt 2 / 2) = log (Real.sqrt 2) - log (2 : ℝ) := by 
      rw [log_div (by positivity) (by positivity)]
    have h4 : log (Real.sqrt 2) = (1 / 2) * log (2 : ℝ) := by 
      have h5 : Real.sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h5]
      have h6 : log ((2 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * log (2 : ℝ) := by 
        rw [log_rpow]
        all_goals norm_num
      linarith
    rw [h3, h4]
    have h5 : log (8 : ℝ) = 3 * log (2 : ℝ) := by 
      calc
        log (8 : ℝ) = log (2 ^ 3) := by 
          norm_num
        _ = 3 * log (2 : ℝ) := by 
          simp [log_pow]
    rw [h5]
    have hpos1 : log (2 : ℝ) > 0 := by 
      apply log_pos
      all_goals linarith
    field_simp [hpos1]
    <;> ring
  have h2 : logb 3 (Real.sqrt 3 / 3) = -1 / 2 := by
    have h3 : logb 3 (Real.sqrt 3 / 3) = (log (Real.sqrt 3 / 3)) / (log (3 : ℝ)) := by 
      field_simp [logb]
    rw [h3]
    have h4 : log (Real.sqrt 3 / 3) = log (Real.sqrt 3) - log (3 : ℝ) := by 
      rw [log_div (by positivity) (by positivity)]
    have h5 : log (Real.sqrt 3) = (1 / 2) * log (3 : ℝ) := by 
      have h6 : Real.sqrt (3 : ℝ) = (3 : ℝ) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h6]
      have h7 : log ((3 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * log (3 : ℝ) := by 
        rw [log_rpow]
        all_goals norm_num
      linarith
    rw [h4, h5]
    have h6 : log (3 : ℝ) > 0 := by 
      apply log_pos
      all_goals linarith
    field_simp [h6]
    <;> ring
  have h4 : logb 8 (Real.sqrt 2 / 2) - logb 3 (Real.sqrt 3 / 3) = 1 / 3 := by
    rw [h1, h2]
    norm_num
  have h5 : logb (Real.sqrt 3 / 3) (1 / 3) = 2 := by
    have h7 : logb (Real.sqrt 3 / 3) (1 / 3) = 2 := by 
      rw [logb]
      have h8 : log (1 / 3 : ℝ) = - log (3 : ℝ) := by 
        simp [log_div, show (3 : ℝ) ≠ 0 by linarith, show (1 : ℝ) ≠ 0 by linarith]
      have h9 : log (Real.sqrt 3 / 3 : ℝ) = - (1 / 2) * log (3 : ℝ) := by 
        have h10 : log (Real.sqrt 3 / (3 : ℝ)) = log (Real.sqrt 3) - log (3 : ℝ) := by 
          rw [log_div (by positivity) (by positivity)]
        have h11 : log (Real.sqrt 3) = (1 / 2) * log (3 : ℝ) := by 
          have h5 : Real.sqrt (3 : ℝ) = (3 : ℝ) ^ (1 / 2 : ℝ) := by 
            rw [Real.sqrt_eq_rpow]
          rw [h5]
          have h6 : log ((3 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * log (3 : ℝ) := by 
            rw [log_rpow]
            all_goals norm_num
          linarith
        rw [h10, h11]
        all_goals ring
      rw [h8, h9]
      have h12 : log (3 : ℝ) ≠ 0 := by 
        have h13 : log (3 : ℝ) > 0 := by 
          apply log_pos
          all_goals norm_num
        linarith
      field_simp [h12]
      <;> ring
    linarith
  rw [h4]
  exact h5