import Mathlib

theorem algebra_7801 : (1 : ℂ) = -1 ↔ False := by
  have h1 : (1 : ℂ) ≠ -1 := by
    norm_num [Complex.ext_iff]
  simp [h1]