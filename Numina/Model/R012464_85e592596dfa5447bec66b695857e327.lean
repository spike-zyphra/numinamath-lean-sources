import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_284082 {x : ℝ} (hx : x ≥ 1) :
    sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1 ↔
    5 ≤ x ∧ x ≤ 10 := by
  constructor
  · -- Assume sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1, prove 5 ≤ x ∧ x ≤ 10
    intro h_eq
    have h1 : x - 1 ≥ 0 := by linarith
    have h2 : sqrt (x + 3 - 4 * sqrt (x - 1)) = abs (sqrt (x - 1) - 2) := by
      have h3 : x + 3 - 4 * sqrt (x - 1) = (sqrt (x - 1) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    have h3 : sqrt (x + 8 - 6 * sqrt (x - 1)) = abs (sqrt (x - 1) - 3) := by
      have h4 : x + 8 - 6 * sqrt (x - 1) = (sqrt (x - 1) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
      rw [h4]
      rw [Real.sqrt_sq_eq_abs]
    rw [h2, h3] at h_eq
    by_cases h5 : sqrt (x - 1) ≥ 3
    · -- sqrt(x - 1) ≥ 3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h_eq
      constructor
      · nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
      · nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
    · -- sqrt(x - 1) < 3
      by_cases h6 : sqrt (x - 1) ≥ 2
      · -- 2 ≤ sqrt(x - 1) < 3
        rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at h_eq
        constructor
        · nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
        · nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
      · -- sqrt (x - 1) < 2
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h_eq
        constructor
        · nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
        · nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
  · -- Assume 5 ≤ x ∧ x ≤ 10, prove sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1
    rintro ⟨hx1, hx2⟩
    have h1 : x - 1 ≥ 0 := by linarith
    have h2 : sqrt (x + 3 - 4 * sqrt (x - 1)) = abs (sqrt (x - 1) - 2) := by
      have h3 : x + 3 - 4 * sqrt (x - 1) = (sqrt (x - 1) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    have h3 : sqrt (x + 8 - 6 * sqrt (x - 1)) = abs (sqrt (x - 1) - 3) := by
      have h4 : x + 8 - 6 * sqrt (x - 1) = (sqrt (x - 1) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
      rw [h4]
      rw [Real.sqrt_sq_eq_abs]
    rw [h2, h3]
    have h4 : 2 ≤ sqrt (x - 1) := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
    have h5 : sqrt (x - 1) ≤ 3 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
    have h4' : abs (sqrt (x - 1) - 2) = sqrt (x - 1) - 2 := by
      rw [abs_of_nonneg]
      linarith
    have h5' : abs (sqrt (x - 1) - 3) = 3 - sqrt (x - 1) := by
      rw [abs_of_nonpos]
      linarith
      all_goals linarith
    rw [h4', h5']
    all_goals linarith