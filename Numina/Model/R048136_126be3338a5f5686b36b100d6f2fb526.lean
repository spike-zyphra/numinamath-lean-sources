import Mathlib

theorem number_theory_9797 : round (((14321 : ℝ) ^ ((1 : ℝ) / 4))) = 11 := by
  have h1 : (14321 : ℝ) ^ ((1 : ℝ) / 4) < 11.5 := by
    have h2 : (14321 : ℝ) < (11.5 : ℝ) ^ (4 : ℝ) := by norm_num
    have h3 : (14321 : ℝ) ^ ((1 : ℝ) / 4) < (11.5 : ℝ) := by
      have h4 : (14321 : ℝ) < (11.5 : ℝ) ^ (4 : ℝ) := h2
      have h5 : (14321 : ℝ) ^ ((1 : ℝ) / 4) < ((11.5 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
        apply Real.rpow_lt_rpow
        all_goals nlinarith
      have h6 : ((11.5 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = (11.5 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith
      linarith [h5, h6]
    linarith
  have h2 : (10.5 : ℝ) < (14321 : ℝ) ^ ((1 : ℝ) / 4) := by
    have h3 : (10.5 : ℝ) ^ (4 : ℝ) < (14321 : ℝ) := by norm_num
    have h4 : (10.5 : ℝ) < (14321 : ℝ) ^ ((1 : ℝ) / 4) := by
      have h5 : (10.5 : ℝ) ^ (4 : ℝ) < (14321 : ℝ) := h3
      have h6 : (10.5 : ℝ) = ((10.5 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals
          norm_num
      have h7 : ((10.5 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) < (14321 : ℝ) ^ ((1 : ℝ) / 4) := by
        apply Real.rpow_lt_rpow
        all_goals
          nlinarith
      linarith [h6, h7]
    linarith
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> (try norm_num)
  all_goals
    try linarith [h1, h2]