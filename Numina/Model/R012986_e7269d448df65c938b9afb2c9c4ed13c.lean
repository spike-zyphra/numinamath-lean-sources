import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_180295 (m : ℝ) :
  (∀ x : ℝ, 4*x^2 - (3*m+1)*x - m - 2 = 0 → -1 < x ∧ x < 2) ↔
  -3/2 < m ∧ m < 12/7 := by
  constructor
  · -- Assume that all roots are in (-1, 2), prove -3/2 < m ∧ m < 12/7
    intro h
    have h1 := h ((3 * m + 1 - Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8) (by
      have h1 : 4 * ((3 * m + 1 - Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8) ^ 2 - (3 * m + 1) * ((3 * m + 1 - Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8) - m - 2 = 0 := by
        nlinarith [Real.sqrt_nonneg (9 * m ^ 2 + 22 * m + 33), Real.sq_sqrt (show 0 ≤ (9 * m ^ 2 + 22 * m + 33 : ℝ) by nlinarith)]
      linarith
    )
    have h2 := h ((3 * m + 1 + Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8) (by
      have h2 : 4 * ((3 * m + 1 + Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8) ^ 2 - (3 * m + 1) * ((3 * m + 1 + Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8) - m - 2 = 0 := by 
        nlinarith [Real.sqrt_nonneg (9 * m ^ 2 + 22 * m + 33), Real.sq_sqrt (show 0 ≤ (9 * m ^ 2 + 22 * m + 33 : ℝ) by nlinarith)]
      linarith
    )
    constructor
    · -- Show -3/2 < m
      nlinarith [Real.sqrt_nonneg (9 * m ^ 2 + 22 * m + 33), Real.sq_sqrt (show 0 ≤ (9 * m ^ 2 + 22 * m + 33 : ℝ) by nlinarith)]
    · -- Show m < 12/7
      nlinarith [Real.sqrt_nonneg (9 * m ^ 2 + 22 * m + 33), Real.sq_sqrt (show 0 ≤ (9 * m ^ 2 + 22 * m + 33 : ℝ) by nlinarith)]
  · -- Assume -3/2 < m ∧ m < 12/7, prove that all roots satisfy -1 < x ∧ x < 2
    rintro ⟨hm1, hm2⟩
    intro x hx
    have h1 : 4*x^2 - (3*m+1)*x - m - 2 = 0 := hx
    constructor
    · -- Show -1 < x
      by_contra h
      push_neg at h
      have h3 : x ≤ -1 := by linarith
      nlinarith [sq_nonneg (x - (3 * m + 1) / 8), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x - (3 * m + 1 - Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8), sq_nonneg (x - (3 * m + 1 + Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8), Real.sqrt_nonneg (9 * m ^ 2 + 22 * m + 33), Real.sq_sqrt (show 0 ≤ (9 * m ^ 2 + 22 * m + 33 : ℝ) by nlinarith)]
    · -- Show x < 2
      by_contra h
      push_neg at h
      have h4 : x ≥ 2 := by linarith
      nlinarith [sq_nonneg (x - (3 * m + 1) / 8), sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x - (3 * m + 1 - Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8), sq_nonneg (x - (3 * m + 1 + Real.sqrt (9 * m ^ 2 + 22 * m + 33)) / 8), Real.sqrt_nonneg (9 * m ^ 2 + 22 * m + 33), Real.sq_sqrt (show 0 ≤ (9 * m ^ 2 + 22 * m + 33 : ℝ) by nlinarith)]