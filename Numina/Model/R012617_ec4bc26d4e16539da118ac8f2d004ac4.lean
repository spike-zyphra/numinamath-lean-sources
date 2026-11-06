import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_147294 (x : ℝ) :
  abs (x^2 - 2) ≤ 2 * x + 1 ↔ (sqrt 2 - 1 ≤ x ∧ x ≤ 3) := by
  constructor
  · -- Assume abs (x^2 - 2) ≤ 2 * x + 1, prove (sqrt 2 - 1 ≤ x ∧ x ≤ 3)
    intro h
    cases' abs_le.mp h with h1 h2
    have h3 : x^2 - 2 ≤ 2 * x + 1 := by linarith
    have h4 : - (2 * x + 1) ≤ x^2 - 2 := by linarith
    constructor
    · -- Show sqrt 2 - 1 ≤ x
      nlinarith [sq_nonneg (x + 1), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x + 1 - sqrt 2), Real.sqrt_nonneg 2]
    · -- Show x ≤ 3
      nlinarith
  · -- Assume (sqrt 2 - 1 ≤ x ∧ x ≤ 3), prove abs (x^2 - 2) ≤ 2 * x + 1
    rintro ⟨h1, h2⟩
    have h3 : x^2 - 2 ≤ 2 * x + 1 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 3), sq_nonneg (x + 1), Real.sqrt_nonneg 2]
    have h4 : - (2 * x + 1) ≤ x^2 - 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - (-1 + Real.sqrt 2)), Real.sqrt_nonneg 2]
    rw [abs_le]
    constructor <;> nlinarith