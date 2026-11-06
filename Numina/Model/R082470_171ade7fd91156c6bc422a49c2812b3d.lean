import Mathlib

theorem algebra_18938 {a : ℝ} (ha : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [ha]
  have h1 : ((8 : ℝ) ^ 2 : ℝ) = (64 : ℝ) := by norm_num
  have h2 : ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
    rw [h1]
    have h3 : ((64 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
      have h4 : (64 : ℝ) = (4 ^ (3 : ℝ)) := by norm_num
      rw [h4]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith
  have h3 : (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) = (64 : ℝ) := by
    rw [h2]
    norm_num
  rw [h3]
  have h4 : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
    have h5 : (64 : ℝ) = (4 ^ (3 : ℝ)) := by norm_num
    rw [h5]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  rw [h4]
  <;> try norm_num