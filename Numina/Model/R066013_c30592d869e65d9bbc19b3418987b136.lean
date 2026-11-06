import Mathlib

theorem algebra_120999 (x : ℝ) (hx : x > 0) :
    ((x * 1.69) ^ ((1 : ℝ) / 2) - (x ^ ((1 : ℝ) / 2))) / (x ^ ((1 : ℝ) / 2)) * 100 = 30 := by
  have h1 : (x * 1.69 : ℝ) ^ ((1 : ℝ) / 2) = (x ^ ((1 : ℝ) / 2) * (1.69 ^ ((1 : ℝ) / 2))) := by
    rw [← Real.mul_rpow]
    all_goals
      linarith [show 0 ≤ (x : ℝ) by linarith, show 0 ≤ (1.69 : ℝ) by norm_num]
  have h2 : (1.69 : ℝ) ^ ((1 : ℝ) / 2) = (1.3 : ℝ) := by
    have h1 : (1.69 : ℝ) = (1.3 : ℝ) ^ 2 := by norm_num
    rw [h1]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_num
    all_goals
      norm_num
  rw [h1, h2]
  have h3 : x ^ ((1 : ℝ) / 2) > 0 := by
    apply Real.rpow_pos_of_pos
    linarith
  field_simp [h3]
  <;> ring_nf <;> norm_num <;> all_goals linarith [h3]