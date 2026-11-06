import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_252562 {x : ℝ} (hx : 0 ≤ x - 1) :
    sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1 ↔
    5 ≤ x ∧ x ≤ 10 := by
  constructor
  · -- Assume sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1, prove 5 ≤ x ∧ x ≤ 10
    intro h
    have h2 : x + 3 - 4 * sqrt (x - 1) = (sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h3 : x + 8 - 6 * sqrt (x - 1) = (sqrt (x - 1) - 3) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h4 : sqrt (x + 3 - 4 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 2) ^ 2) := by
      rw [h2]
    have h5 : sqrt (x + 8 - 6 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 3) ^ 2) := by
      rw [h3]
    have h6 : sqrt ((sqrt (x - 1) - 2) ^ 2) = |sqrt (x - 1) - 2| := by 
      rw [Real.sqrt_sq_eq_abs]
    have h7 : sqrt ((sqrt (x - 1) - 3) ^ 2) = |sqrt (x - 1) - 3| := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h4, h5, h6, h7] at h
    have hy1 : 2 ≤ sqrt (x - 1) ∧ sqrt (x - 1) ≤ 3 := by
      by_cases h8 : sqrt (x - 1) ≥ 3
      · -- Case sqrt(x - 1) ≥ 3
        rw [abs_of_nonneg (by linarith : sqrt (x - 1) - 2 ≥ 0), abs_of_nonneg (by linarith : sqrt (x - 1) - 3 ≥ 0)] at h
        constructor
        · nlinarith
        · linarith
      · -- Case 2 ≤ sqrt(x - 1) < 3
        by_cases h9 : sqrt (x - 1) ≥ 2
        · -- Case 2 ≤ sqrt(x - 1) < 3
          rw [abs_of_nonneg (by linarith : sqrt (x - 1) - 2 ≥ 0), abs_of_nonpos (by linarith : sqrt (x - 1) - 3 ≤ 0)] at h
          constructor
          · nlinarith
          · nlinarith
        · -- Case sqrt(x - 1) < 2
          rw [abs_of_nonpos (by linarith : sqrt (x - 1) - 2 ≤ 0), abs_of_nonpos (by linarith : sqrt (x - 1) - 3 ≤ 0)] at h
          constructor
          · nlinarith
          · nlinarith
    have h8 : 2 ≤ sqrt (x - 1) := hy1.1
    have h9 : sqrt (x - 1) ≤ 3 := hy1.2
    have h10 : 4 ≤ x - 1 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), h8]
    have h11 : x - 1 ≤ 9 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), h9]
    constructor
    · nlinarith
    · nlinarith
  · -- Assume 5 ≤ x ∧ x ≤ 10, prove sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1
    rintro ⟨h5, h10⟩
    have h2 : x + 3 - 4 * sqrt (x - 1) = (sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h3 : x + 8 - 6 * sqrt (x - 1) = (sqrt (x - 1) - 3) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h4 : sqrt (x + 3 - 4 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 2) ^ 2) := by
      rw [h2]
    have h5 : sqrt (x + 8 - 6 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 3) ^ 2) := by
      rw [h3]
    have h6 : sqrt ((sqrt (x - 1) - 2) ^ 2) = |sqrt (x - 1) - 2| := by 
      rw [Real.sqrt_sq_eq_abs]
    have h7 : sqrt ((sqrt (x - 1) - 3) ^ 2) = |sqrt (x - 1) - 3| := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h4, h5, h6, h7]
    have hy1 : 2 ≤ sqrt (x - 1) := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), h5]
    have h9 : sqrt (x - 1) ≤ 3 := by
      have h8 : x - 1 ≤ 9 := by linarith
      have h9 : sqrt (x - 1) ≤ sqrt 9 := Real.sqrt_le_sqrt (by linarith)
      have h10 : sqrt 9 = 3 := Real.sqrt_eq_cases.2 (by norm_num)
      linarith [Real.sqrt_nonneg 9]
    have h10 : sqrt (x - 1) - 2 ≥ 0 := by nlinarith
    have h11 : sqrt (x - 1) - 3 ≤ 0 := by nlinarith
    have h12 : |sqrt (x - 1) - 2| = sqrt (x - 1) - 2 := by
      rw [abs_of_nonneg h10]
    have h13 : |sqrt (x - 1) - 3| = 3 - sqrt (x - 1) := by
      rw [abs_of_nonpos h11]
      all_goals linarith
    rw [h12, h13]
    nlinarith