import Mathlib

theorem algebra_328135 (k : ℝ) :
    ∃ a b : ℝ, a + 3 * b - 1 = 0 ∧ a^2 + b^2 - 4 * a - 6 * b + 13 - k = 0 ↔ k ≥ 10 := by
  by_cases h : k ≥ 10
  · -- Assume k >= 10, we need to show there exist real numbers a and b
    use 1 - 3 * Real.sqrt ((k - 10) / 10), Real.sqrt ((k - 10) / 10)
    constructor
    · -- Assume the equations hold, prove k >= 10 (trivial since k >= 10)
      rintro ⟨h1, h2⟩
      linarith
    · -- Assume k >= 10, prove the equations hold
      intro hk
      constructor
      · -- Show a + 3 * b -1 = 0
        nlinarith [Real.sqrt_nonneg ((k - 10) / 10), Real.sq_sqrt (show (0 : ℝ) ≤ (k - 10) / 10 by nlinarith)]
      · -- Show a^2 + b^2 -4 * a -6 * b +13 -k =0
        nlinarith [Real.sqrt_nonneg ((k - 10) / 10), Real.sq_sqrt (show (0 : ℝ) ≤ (k - 10) / 10 by nlinarith)]
  · -- Assume k < 10, we need to show the biimplication is true by contradiction
    use (0 : ℝ), (1 / 3 : ℝ)
    constructor
    · -- Assume the equations hold, prove k >= 10 (contradicts k < 10)
      rintro ⟨h1, h2⟩
      nlinarith [Real.sqrt_nonneg ((10 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    · -- Assume k >= 10, prove the equations hold (contradicts k < 10)
      intro hk
      linarith