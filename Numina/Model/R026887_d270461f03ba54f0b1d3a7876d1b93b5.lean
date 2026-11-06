import Mathlib

theorem algebra_600388 (P : ℝ × ℝ) (hP : abs (5 * P.1 + P.2) + abs (5 * P.1 - P.2) = 20) :
    P.1 ^ 2 - P.1 * P.2 + P.2 ^ 2 ≤ 124 ∧ P.1 ^ 2 - P.1 * P.2 + P.2 ^ 2 ≥ 3 := by
  by_cases h1 : (5 * P.1 + P.2) ≥ 0
  · -- Case 1: `5 * P.1 + P.2 ≥ 0`
    rw [abs_of_nonneg h1] at hP
    by_cases h2 : (5 * P.1 - P.2) ≥ 0
    · -- Case 1a: `5 * P.1 - P.2 ≥ 0`
      rw [abs_of_nonneg h2] at hP
      have h_eq1 : P.1 = 2 := by linarith
      have hx1 : P.1 ^ 2 - P.1 * P.2 + P.2 ^ 2 = P.2 ^ 2 - 2 * P.2 + 4 := by
        rw [h_eq1]
        ring
      have h3 : P.2 ≥ -10 := by
        nlinarith
      have h4 : P.2 ≤ 10 := by
        nlinarith
      constructor
      · nlinarith [sq_nonneg (P.2 + 10), sq_nonneg (P.2 - 10), sq_nonneg (P.2 - 1)]
      · nlinarith [sq_nonneg (P.2 + 10), sq_nonneg (P.2 - 10), sq_nonneg (P.2 - 1)]
    · -- Case 1b: `5 * P.1 - P.2 < 0`
      rw [abs_of_neg (by linarith)] at hP
      have h_eq2 : P.2 = 10 := by
        nlinarith
      have hx2 : P.1 ^ 2 - P.1 * P.2 + P.2 ^ 2 = P.1 ^ 2 - 10 * P.1 + 100 := by
        rw [h_eq2]
        ring
      have h5 : P.1 ≥ -2 := by
        nlinarith
      have h6 : P.1 < 2 := by
        nlinarith
      constructor
      · nlinarith [sq_nonneg (P.1 + 2), sq_nonneg (P.1 - 2), sq_nonneg (P.1 - 5)]
      · nlinarith [sq_nonneg (P.1 + 2), sq_nonneg (P.1 - 2), sq_nonneg (P.1 - 5)]
  · -- Case 2: `5 * P.1 + P.2 < 0`
    rw [abs_of_neg (by linarith)] at hP
    by_cases h2 : (5 * P.1 - P.2) ≥ 0
    · -- Case 2a: `5 * P.1 - P.2 ≥ 0`
      rw [abs_of_nonneg h2] at hP
      have h_eq3 : P.2 = -10 := by
        nlinarith
      have h_eq4 : P.1 ^ 2 - P.1 * P.2 + P.2 ^ 2 = P.1 ^ 2 + 10 * P.1 + 100 := by
        rw [h_eq3]
        ring
      have h7 : P.1 ≥ -2 := by
        nlinarith
      have h8 : P.1 < 2 := by
        nlinarith
      constructor
      · nlinarith [sq_nonneg (P.1 + 2), sq_nonneg (P.1 - 2), sq_nonneg (P.1 - 5)]
      · nlinarith [sq_nonneg (P.1 + 2), sq_nonneg (P.1 - 2), sq_nonneg (P.1 - 5)]
    · -- Case 2b: `5 * P.1 - P.2 < 0`
      rw [abs_of_neg (by linarith)] at hP
      have h_eq5 : P.1 = -2 := by
        nlinarith
      have h_eq6 : P.1 ^ 2 - P.1 * P.2 + P.2 ^ 2 = P.2 ^ 2 + 2 * P.2 + 4 := by
        rw [h_eq5]
        ring
      have h9 : P.2 > -10 := by
        nlinarith
      have h10 : P.2 < 10 := by
        nlinarith
      constructor
      · nlinarith [sq_nonneg (P.2 + 10), sq_nonneg (P.2 - 10), sq_nonneg (P.2 + 1)]
      · nlinarith [sq_nonneg (P.2 + 10), sq_nonneg (P.2 - 10), sq_nonneg (P.2 + 1)]