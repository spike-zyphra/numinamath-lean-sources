import Mathlib

theorem algebra_3273 : ⌊(200 * 203 * 206 * 209 : ℝ).sqrt⌋ = 41808 := by
  have h2 : (200 * 203 * 206 * 209 : ℝ) = (1747992400 : ℝ) := by norm_num
  rw [h2]
  have h3 : 41808 ≤ (1747992400 : ℝ).sqrt := by
    rw [Real.le_sqrt] <;> norm_num
  have h4 : (1747992400 : ℝ).sqrt < 41809 := by
    rw [Real.sqrt_lt] <;> norm_num
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg (1747992400 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1747992400 : ℝ) by norm_num)]