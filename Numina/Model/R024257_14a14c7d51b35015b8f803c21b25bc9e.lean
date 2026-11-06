import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_166752 (a : ℝ) :
  (∀ x : ℝ, x^2 - 2 * x - abs (x - 1 - a) - abs (x - 2) + 4 ≥ 0) ↔
  -2 ≤ a ∧ a ≤ 1 := by
  constructor
  · -- Assume that ∀ x : ℝ, x^2 - 2 * x - abs (x - 1 - a) - abs (x - 2) + 4 ≥ 0
    intro h
    have h1 := h 0
    have h2 := h 1
    have h6 : abs ((0 : ℝ) - 1 - a) = abs (1 + a) := by
      have h7 : (0 : ℝ) - 1 - a = -(1 + a) := by ring
      rw [h7]
      rw [abs_neg]
    have h7 : abs ((1 : ℝ) - 1 - a) = abs (a) := by
      have h8 : (1 : ℝ) - 1 - a = -a := by ring
      rw [h8]
      rw [abs_neg]
    have h8 : abs ((0 : ℝ) - 2) = 2 := by
      norm_num [abs]
    have h9 : abs ((1 : ℝ) - 2) = 1 := by
      norm_num [abs]
    simp only [h6, h8] at h1
    simp only [h7, h9] at h2
    have h01 : -3 ≤ a ∧ a ≤ 1 := by
      cases' abs_le.mp (show abs (1 + a) ≤ 2 by linarith) with h11 h12
      constructor <;> linarith
    have h02 : -2 ≤ a ∧ a ≤ 2 := by
      cases' abs_le.mp (show abs a ≤ 2 by linarith) with h11 h12
      constructor <;> linarith
    constructor
    · -- prove -2 ≤ a
      linarith
    · -- prove a ≤ 1
      linarith
  · -- Assume that -2 ≤ a ∧ a ≤ 1
    rintro ⟨ha1, ha2⟩
    intro x
    by_cases h1 : x - 1 - a ≥ 0
    · -- If x ≥ 1 + a
      rw [abs_of_nonneg h1]
      by_cases h2 : x - 2 ≥ 0
      · -- If x ≥ 2
        rw [abs_of_nonneg h2]
        nlinarith [sq_nonneg (x - 1 - a), sq_nonneg (x - 2), sq_nonneg (a - 1), sq_nonneg (x - 0), sq_nonneg (x - 1), sq_nonneg (x - 2)]
      · -- If x < 2
        rw [abs_of_neg (lt_of_not_ge h2)]
        nlinarith [sq_nonneg (x - 1 - a), sq_nonneg (x - 2), sq_nonneg (a - 1), sq_nonneg (x - 0), sq_nonneg (x - 1), sq_nonneg (x - 2)]
    · -- If x < 1 + a
      rw [abs_of_neg (lt_of_not_ge h1)]
      by_cases h2 : x - 2 ≥ 0
      · -- If x ≥ 2
        rw [abs_of_nonneg h2]
        nlinarith [sq_nonneg (x - 1 - a), sq_nonneg (x - 2), sq_nonneg (a - 1), sq_nonneg (x - 0), sq_nonneg (x - 1), sq_nonneg (x - 2)]
      · -- If x < 2
        rw [abs_of_neg (lt_of_not_ge h2)]
        nlinarith [sq_nonneg (x - 1 - a), sq_nonneg (x - 2), sq_nonneg (a - 1), sq_nonneg (x - 0), sq_nonneg (x - 1), sq_nonneg (x - 2)]