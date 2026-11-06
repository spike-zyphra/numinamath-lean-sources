import Mathlib

open Real

theorem inequalities_260608 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    1 / 2 ≤ (a ^ 3 + b ^ 3) / (a ^ 2 + b ^ 2) ∧ (a ^ 3 + b ^ 3) / (a ^ 2 + b ^ 2) ≤ 1 := by
  have h1 : b = 1 - a := by linarith
  have h2 : a^3 + b^3 = 3 * a ^ 2 - 3 * a + 1 := by
    rw [h1]
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2)]
  have h3 : a^2 + b^2 = 2 * a ^ 2 - 2 * a + 1 := by
    rw [h1]
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2)]
  constructor
  · -- Prove the left inequality: 1/2 ≤ (a^3 + b^3) / (a^2 + b^2)
    rw [h2, h3]
    have h4 : 0 < 2 * a ^ 2 - 2 * a + 1 := by
      nlinarith [sq_nonneg (a - 1 / 2)]
    apply (le_div_iff₀ h4).mpr
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 1), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg ((1 - a) - 0), mul_nonneg ha (show 0 ≤ (1 - a : ℝ) by nlinarith)]
  · -- Prove the right inequality: (a^3 + b^3) / (a^2 + b^2) ≤ 1
    rw [h2, h3]
    have h4 : 0 < 2 * a ^ 2 - 2 * a + 1 := by
      nlinarith [sq_nonneg (a - 1 / 2)]
    apply (div_le_iff₀ h4).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 0), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg ((1 - a) - 0), mul_nonneg ha (show 0 ≤ (1 - a : ℝ) by nlinarith)]