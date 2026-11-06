import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_260266 (x : ℝ) :
  4 + x^2 + 2 * x * sqrt (2 - x^2) < 8 * sqrt (2 - x^2) + 5 * x ∧ 0 ≤ 2 - x^2 ↔
  -1 < x ∧ x ≤ sqrt 2 := by
  constructor
  · -- Assume the conjunction of the inequality and non-negativity of sqrt argument
    rintro ⟨h₁, h₂⟩
    have h3 : x ≤ Real.sqrt 2 := by
      have h3 : x^2 ≤ 2 := by nlinarith
      have h4 : x ≤ Real.sqrt 2 := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      linarith
    have h4 : -1 < x := by
      by_contra h
      push_neg at h
      have h5 : x ≤ -1 := by linarith
      nlinarith [sq_nonneg (sqrt (2 - x^2) - 1), sq_nonneg (x + 1),
                  Real.sqrt_nonneg (2 - x^2), Real.sq_sqrt (show 0 ≤ 2 - x^2 by nlinarith),
                  Real.sqrt_nonneg (2 - x^2), h5]
    constructor <;> linarith
  · -- Assume -1 < x ∧ x ≤ sqrt 2
    rintro ⟨h₁, h₂⟩
    have h3 : x ≤ Real.sqrt 2 := h₂
    have h4 : x ≥ -1 := by linarith
    have h5 : x^2 ≤ 2 := by
      have h5 : x ≤ Real.sqrt 2 := h₂
      have h6 : x ≥ -1 := by linarith
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - Real.sqrt 2)]
    have h6 : 0 ≤ 2 - x^2 := by nlinarith
    constructor
    · -- Show the inequality
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - Real.sqrt 2), sq_nonneg (sqrt (2 - x^2) - 1), sq_nonneg (x + 1),
                  Real.sqrt_nonneg (2 - x^2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 - x^2 by linarith),
                  Real.sqrt_nonneg (2 - x^2), sq_nonneg (x - 4), Real.sqrt_nonneg (2), h₁, h₂]
    · -- Show the non-negativity of sqrt argument
      linarith