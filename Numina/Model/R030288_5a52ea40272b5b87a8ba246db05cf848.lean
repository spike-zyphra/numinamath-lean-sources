import Mathlib

theorem algebra_21301 : (Int.floor ((2 / 9 + 1 / 7 : ℚ) * 10 ^ 20)) % 10 = 6 := by
  have h1 : (2 / 9 + 1 / 7 : ℚ) = (23 / 63 : ℚ) := by
    norm_num
  rw [h1]
  have h2 : Int.floor ((23 / 63 : ℚ) * 10 ^ 20) = 36507936507936507936 := by
    norm_num [Int.floor_eq_iff]
  rw [h2]
  all_goals norm_num