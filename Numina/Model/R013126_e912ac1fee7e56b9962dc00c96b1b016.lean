import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_305938 (x : ℝ) :
  abs (x^2 + 3 * x - 8) > x^2 + 3 * x - 8 ↔
  (-3 - sqrt 41) / 2 < x ∧ x < (-3 + sqrt 41) / 2 := by
  constructor
  · -- Forward direction: If abs (x^2 + 3 * x - 8) > x^2 + 3 * x - 8, then (-3 - sqrt 41) / 2 < x ∧ x < (-3 + sqrt 41) / 2
    intro h
    have h1 : x^2 + 3 * x - 8 < 0 := by
      cases le_or_lt 0 (x^2 + 3 * x - 8) with
      | inl h2 =>
        have h3 : abs (x^2 + 3 * x - 8) = x^2 + 3 * x - 8 := by
          rw [abs_of_nonneg h2]
        linarith [h3, h]
      | inr h2 =>
        have h3 : abs (x^2 + 3 * x - 8) = - (x^2 + 3 * x - 8) := by
          rw [abs_of_neg h2]
        nlinarith [h3, h]
    have h2 : (-3 - Real.sqrt 41) / 2 < x := by
      nlinarith [Real.sqrt_nonneg 41, Real.sq_sqrt (show 0 ≤ (41 : ℝ) by norm_num), sq_nonneg (x + 3 / 2), Real.sqrt_pos.mpr (show (41 : ℝ) > (0 : ℝ) by norm_num)]
    have h3 : x < (-3 + Real.sqrt 41) / 2 := by
      nlinarith [Real.sqrt_nonneg 41, Real.sq_sqrt (show 0 ≤ (41 : ℝ) by norm_num), sq_nonneg (x + 3 / 2), Real.sqrt_pos.mpr (show (41 : ℝ) > (0 : ℝ) by norm_num)]
    constructor <;> linarith
  · -- Backward direction: If (-3 - sqrt 41) / 2 < x ∧ x < (-3 + sqrt 41) / 2, then abs (x^2 + 3 * x - 8) > x^2 + 3 * x - 8
    rintro ⟨h1, h2⟩
    have h3 : x^2 + 3 * x - 8 < 0 := by
      nlinarith [Real.sqrt_nonneg 41, Real.sq_sqrt (show 0 ≤ (41 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (41 : ℝ) > (0 : ℝ) by norm_num), sq_nonneg (x + 3 / 2)]
    have h4 : abs (x^2 + 3 * x - 8) = - (x^2 + 3 * x - 8) := by
      rw [abs_of_neg h3]
    nlinarith [h4, h3]