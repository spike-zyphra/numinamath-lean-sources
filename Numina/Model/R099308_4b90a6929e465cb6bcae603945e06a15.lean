import Mathlib

theorem algebra_19546 (a : ℝ) (ha : a = 13) : (a ^ ((1 : ℝ) / 3)) ^ 6 = 169 := by
  rw [ha]
  have h1 : ((13 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (13 : ℝ) ^ (2 : ℝ) := by
    calc
      ((13 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = ((13 : ℝ) ^ ((1 / 3 : ℝ))) ^ (6 : ℝ) := by
        norm_cast
      _ = (13 : ℝ) ^ ((1 / 3 : ℝ) * (6 : ℝ)) := by
        rw [← Real.rpow_mul]
        all_goals norm_num
      _ = (13 : ℝ) ^ (2 : ℝ) := by
        norm_num
        all_goals norm_num
  rw [h1]
  all_goals norm_num
  <;> try { tauto }