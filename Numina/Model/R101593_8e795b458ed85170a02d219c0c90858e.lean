import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_180393 (x : ℝ) :
  -4 ≤ (x^2 - 2 * x - 3) / (2 * x^2 + 2 * x + 1) ∧
  (x^2 - 2 * x - 3) / (2 * x^2 + 2 * x + 1) ≤ 1 := by
  have h1 : 2 * x^2 + 2 * x + 1 > 0 := by
    nlinarith [sq_nonneg (x : ℝ), sq_nonneg (x + 1 : ℝ)]
  constructor
  · -- Prove the lower bound: -4 ≤ (x^2 - 2 * x - 3) / (2 * x^2 + 2 * x + 1)
    have h2 : -4 * (2 * x^2 + 2 * x + 1) ≤ x^2 - 2 * x - 3 := by
      nlinarith [sq_nonneg (3 * x + 1 : ℝ)]
    have h3 : -4 ≤ (x^2 - 2 * x - 3) / (2 * x^2 + 2 * x + 1) := by
      apply (le_div_iff₀ h1).mpr
      nlinarith [sq_nonneg (3 * x + 1 : ℝ)]
    exact h3
  · -- Prove the upper bound: (x^2 - 2 * x - 3) / (2 * x^2 + 2 * x + 1) ≤ 1
    have h4 : (x^2 - 2 * x - 3) ≤ (2 * x^2 + 2 * x + 1) := by
      nlinarith [sq_nonneg (x + 2 : ℝ)]
    have h5 : (x^2 - 2 * x - 3) / (2 * x^2 + 2 * x + 1) ≤ 1 := by
      apply (div_le_iff₀ h1).mpr
      nlinarith [sq_nonneg (x + 2 : ℝ)]
    exact h5