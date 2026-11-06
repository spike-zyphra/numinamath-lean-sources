import Mathlib

open Real

theorem number_theory_95224 : 3 / 10 < logb 10 2 ∧ logb 10 2 < 4 / 13 := by
  have h1 : 3 / 10 < logb 10 2 := by
    have h2 : logb 10 (2 ^ 10) > logb 10 (10 ^ 3) := by 
      have h3 : (2 ^ 10 : ℝ) > (10 ^ 3 : ℝ) := by
        norm_num
      have h4 : logb 10 (2 ^ 10) > logb 10 (10 ^ 3) := by 
        apply Real.logb_lt_logb
        all_goals 
          try norm_num 
          all_goals
            try linarith
      linarith [h4]
    have h5 : logb 10 (2 ^ 10) = 10 * logb 10 2 := by
      simp [logb_pow, mul_comm]
      <;> ring_nf
    have h6 : logb 10 (10 ^ 3) = (3 : ℝ) := by
      simp [logb_pow]
    linarith [h2, h5, h6]

  have h7 : logb 10 2 < 4 / 13 := by
    have h8 : logb 10 (2 ^ 13) < logb 10 (10 ^ 4) := by 
      have h9 : (2 ^ 13 : ℝ) < (10 ^ 4 : ℝ) := by
        norm_num
      have h10 : logb 10 (2 ^ 13) < logb 10 (10 ^ 4) := by 
        apply Real.logb_lt_logb
        all_goals 
          try norm_num 
          all_goals
            try linarith 
      linarith [h10]
    have h5 : logb 10 (2 ^ 13) = 13 * logb 10 2 := by
      simp [logb_pow, mul_comm]
      <;> ring_nf
    have h6 : logb 10 (10 ^ 4) = (4 : ℝ) := by
      simp [logb_pow]
    linarith [h8, h5, h6]

  constructor
  · linarith 
  · linarith