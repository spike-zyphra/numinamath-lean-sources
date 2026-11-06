import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_290267 : IsLeast {t : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ t = (x + 1 / y) * (x + 1 / y - 2018) +
    (y + 1 / x) * (y + 1 / x - 2018)} (-2018 ^ 2 / 2) := by
  constructor
  · -- Show that -2018^2 / 2 is in the set.
    use (1009 + Real.sqrt 1018077) / 2, (1009 + Real.sqrt 1018077) / 2
    constructor
    · -- Show that (1009 + Real.sqrt 1018077) / 2 is positive.
      nlinarith [Real.sqrt_pos.mpr (show 0 < (1018077 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1018077 : ℝ) by norm_num)]
    constructor
    · -- Show that (1009 + Real.sqrt 1018077) / 2 is positive.
      nlinarith [Real.sqrt_pos.mpr (show 0 < (1018077 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1018077 : ℝ) by norm_num)]
    · -- Verify the value.
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show 0 < (1018077 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1018077 : ℝ) by norm_num), sq_nonneg (Real.sqrt 1018077 - 1009)]
  · -- Show that -2018^2 / 2 is the smallest element in the set.
    intro t ht
    rcases ht with ⟨x, y, hx, hy, ht⟩
    have h1 : (x + 1 / y) * (x + 1 / y - 2018) + (y + 1 / x) * (y + 1 / x - 2018) ≥ -2018 ^ 2 / 2 := by
      have h11 : (x + 1 / y) * (x + 1 / y - 2018) + (y + 1 / x) * (y + 1 / x - 2018) =
          (x + 1 / y - 1009)^2 + (y + 1 / x - 1009)^2 - 2 * 1009^2 := by ring
      rw [h11]
      nlinarith [sq_nonneg (x + 1 / y - 1009), sq_nonneg (y + 1 / x - 1009)]
    linarith