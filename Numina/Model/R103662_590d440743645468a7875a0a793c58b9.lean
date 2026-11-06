import Mathlib

theorem inequalities_276973 (a : ℝ) (ha : 0 < a) :
    2 * a / (1 + a ^ 2) ≤ 1 := by
  have h1 : 0 < 1 + a ^ 2 := by
    nlinarith [sq_pos_of_pos ha]
  have h2 : 2 * a ≤ 1 + a ^ 2 := by
    nlinarith [sq_nonneg (a - 1)]
  apply (div_le_iff₀ h1).mpr
  linarith