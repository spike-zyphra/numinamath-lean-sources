import Mathlib

theorem algebra_198805 {k : ℝ} (hk : k ≠ 0) (h : Real.sqrt ((50 + 120 + 130) / 2 * (150 - 50) * (150 - 120) * (150 - 130)) = 50 * 130 * k / 2) :
    k / Real.sqrt (1 - k ^ 2) = 12 / 5 := by
  have h1 : Real.sqrt ((50 + 120 + 130 : ℝ) / 2 * (150 - 50) * (150 - 120) * (150 - 130)) = 3000 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : 50 * 130 * k / 2 = 3000 := by
    linarith [h, h1]
  have hk_val : k = 12 / 13 := by
    linarith
  have hk2 : k ^ 2 = (144 / 169 : ℝ) := by
    rw [hk_val]
    norm_num
  have h1mk2 : (1 - k ^ 2 : ℝ) = (25 / 169 : ℝ) := by
    linarith [hk2]
  have hsqrt : Real.sqrt (1 - k ^ 2) = (5 / 13 : ℝ) := by
    rw [h1mk2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [hsqrt, hk_val]
  field_simp
  <;> norm_num