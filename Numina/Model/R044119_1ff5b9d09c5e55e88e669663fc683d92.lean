import Mathlib

theorem algebra_13737 (x : ℝ) (hx : x = ∑' n : ℕ, 54 * 0.01 ^ n) :
    round (x * 100) / 100 = (54.55 : ℝ) := by
  have h1 : x = (54 / (1 - (0.01 : ℝ))) := by 
    rw [hx]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  have h2 : x = (5400 / 99 : ℝ) := by
    rw [h1]
    norm_num
  have h3 : x * 100 = (540000 / 99 : ℝ) := by
    rw [h2]
    field_simp
    <;> norm_num
  have h4 : round (x * 100) = (5455 : ℝ) := by
    rw [h3]
    norm_num [round_eq]
    <;> norm_num
  rw [h4]
  all_goals norm_num