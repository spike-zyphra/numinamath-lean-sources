import Mathlib

theorem number_theory_9588 (n : ℝ) (h : n = 20232023) :
    round ((n) ^ ((1 : ℝ) / 8)) = 8 := by
  rw [h]
  have h1 : (20232023 : ℝ) ^ ((1 : ℝ) / 8) < (8.5 : ℝ) := by
    have h2 : (20232023 : ℝ) < (8.5 : ℝ) ^ (8 : ℝ) := by norm_num
    have h3 : (20232023 : ℝ) ^ ((1 : ℝ) / 8) < ( (8.5 : ℝ) ^ (8 : ℝ) ) ^ ((1 : ℝ) / 8) := by
      apply Real.rpow_lt_rpow
      all_goals
        linarith
    have h4 : ( ( (8.5 : ℝ) ^ (8 : ℝ) ) ^ ((1 : ℝ) / 8) ) = (8.5 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals
        linarith
    linarith
  have h4 : (20232023 : ℝ) ^ ((1 : ℝ) / 8) > (7.5 : ℝ) := by
    have h5 : (20232023 : ℝ) > (7.5 : ℝ) ^ (8 : ℝ) := by norm_num
    have h6 : (20232023 : ℝ) ^ ((1 : ℝ) / 8) > ( (7.5 : ℝ) ^ (8 : ℝ) ) ^ ((1 : ℝ) / 8) := by
      apply Real.rpow_lt_rpow
      all_goals
        linarith
    have h7 : ( ( (7.5 : ℝ) ^ (8 : ℝ) ) ^ ((1 : ℝ) / 8) ) = (7.5 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals
        linarith
    linarith
  have h7 : 7.5 < (20232023 : ℝ) ^ ((1 : ℝ) / 8) := by linarith [h4]
  have h8 : (20232023 : ℝ) ^ ((1 : ℝ) / 8) < 8.5 := by linarith [h1]
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> (try linarith)