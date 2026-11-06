import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327685 : logb (sqrt 2) (sin (7 * π / 8)) + logb (sqrt 2) (sin (3 * π / 8)) = -3 := by
  have h1 : sin (7 * π / 8) = sin (π / 8) := by 
    have h2 : 7 * π / 8 = π - (π / 8) := by 
      ring
    rw [h2]
    rw [sin_pi_sub]

  have h3 : sin (π / 8) * sin (3 * π / 8) = Real.sqrt 2 / 4 := by
    have h4 : sin (3 * π / 8) = cos (π / 8) := by 
      have h5 : 3 * π / 8 = π / 2 - (π / 8) := by 
        nlinarith [Real.pi_pos]
      rw [h5]
      rw [sin_pi_div_two_sub]
    rw [h4]
    have h5 : sin (π / 8) * cos (π / 8) = (1 / 2) * sin (2 * (π / 8)) := by
      rw [sin_two_mul]
      all_goals nlinarith 
    have h6 : sin (2 * (π / 8)) = Real.sqrt 2 / 2 := by
      have h7 : 2 * (π / 8) = π / 4 := by 
        nlinarith 
      rw [h7]
      exact sin_pi_div_four
    rw [h5, h6]
    all_goals nlinarith
  
  have h2 : logb (sqrt 2) (sin (7 * π / 8)) + logb (sqrt 2) (sin (3 * π / 8)) = 
        logb (sqrt 2) (sin (7 * π / 8) * sin (3 * π / 8)) := by 
    rw [← logb_mul (by 
      have h3 : sin (7 * π / 8) > 0 := by 
        have h1 : sin (7 * π / 8) = sin (π / 8) := by 
          have h2 : 7 * π / 8 = π - (π / 8) := by 
            ring 
          rw [h2]
          rw [sin_pi_sub]
        rw [h1]
        apply sin_pos_of_pos_of_lt_pi 
        nlinarith [Real.pi_pos]
        nlinarith [Real.pi_pos]
      linarith 
    ) (by 
      have h41 : sin (3 * π / 8) > 0 := by 
        apply sin_pos_of_pos_of_lt_pi 
        nlinarith [Real.pi_pos]
        nlinarith [Real.pi_pos]
      linarith
    )
  ]
  rw [h2]
  have h4_sin_mul : sin (7 * π / 8) * sin (3 * π / 8) = Real.sqrt 2 / 4 := by 
    calc
      sin (7 * π / 8) * sin (3 * π / 8) 
        = sin (π / 8) * sin (3 * π / 8) := by 
          rw [h1]
      _ = Real.sqrt 2 / 4 := by 
        nlinarith [h3] 
  rw [h4_sin_mul]
  have h50 : logb (sqrt 2) (Real.sqrt 2 / 4) = -3 := by
    have h70 : logb (sqrt 2) (Real.sqrt 2 / 4) = (log (Real.sqrt 2 / 4)) / (log (sqrt 2)) := by 
      field_simp [logb]
    have h80 : log (Real.sqrt 2 / 4) = log (Real.sqrt 2) - log (4 : ℝ) := by 
      rw [log_div (by positivity) (by positivity)]
    have h90 : log (4 : ℝ) = 2 * log (2 : ℝ) := by 
      calc 
        log (4 : ℝ) = log ((2 : ℝ) ^ 2) := by norm_num 
        _ = 2 * log (2 : ℝ) := by simp [log_pow]
        _ = 2 * log (2 : ℝ) := by ring 
    have h100 : log (Real.sqrt 2) = (1 / 2) * log (2 : ℝ) := by 
      rw [Real.sqrt_eq_rpow]
      rw [log_rpow]
      all_goals linarith 
    rw [h70]
    rw [h80, h90, h100]
    have h140 : log (2 : ℝ) > 0 := by 
      apply log_pos
      linarith 
    field_simp [h140]
    all_goals nlinarith 
  exact h50