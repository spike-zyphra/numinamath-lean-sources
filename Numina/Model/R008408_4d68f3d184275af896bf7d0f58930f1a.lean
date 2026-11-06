import Mathlib


theorem algebra_14842 {z : ℂ} (h : z * (5 + 3 * .I) = 32 - 8 * .I) :
    z = 4 - 4 * .I := by
  have hz : z = (32 - 8 * Complex.I) / (5 + 3 * Complex.I) := by
    rw [←h]
    field_simp [Complex.ext_iff, Complex.I_mul_I]
    all_goals norm_num
  rw [hz]
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  all_goals norm_num
  <;> norm_num [Complex.ext_iff]