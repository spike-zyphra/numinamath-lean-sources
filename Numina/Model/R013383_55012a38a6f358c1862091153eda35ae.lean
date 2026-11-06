import Mathlib

theorem algebra_233152 (x : ℝ) :
    max (max (max ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2))) ((x + 1 / 3) * (x - 1 / 3))) ((x + 1 / 4) * (x - 1 / 4)) = (x + 1 / 4) * (x - 1 / 4) := by
  have h1 : (x + 1) * (x - 1) ≤ (x + 1 / 4) * (x - 1 / 4) := by
    nlinarith [sq_nonneg (x), sq_nonneg (x + 1 / 4), sq_nonneg (x - 1 / 4), sq_nonneg (x - 1)]
  have h2 : (x + 1 / 2) * (x - 1 / 2) ≤ (x + 1 / 4) * (x - 1 / 4) := by
    nlinarith [sq_nonneg (x), sq_nonneg (x + 1 / 4), sq_nonneg (x - 1 / 4), sq_nonneg (x - 1 / 2)]
  have h3 : (x + 1 / 3) * (x - 1 / 3) ≤ (x + 1 / 4) * (x - 1 / 4) := by
    nlinarith [sq_nonneg (x), sq_nonneg (x + 1 / 4), sq_nonneg (x - 1 / 4), sq_nonneg (x - 1 / 3)]
  have h4 : max ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2)) ≤ (x + 1 / 4) * (x - 1 / 4) := by
    cases' max_cases ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2)) with h5 h5
    · -- Assume max ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2)) = (x + 1) * (x - 1)
      nlinarith [h1]
    · -- Assume max ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2)) = (x + 1 / 2) * (x - 1 / 2)
      nlinarith [h2]
  have h5 : max (max ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2))) ((x + 1 / 3) * (x - 1 / 3)) ≤ (x + 1 / 4) * (x - 1 / 4) := by
    cases' max_cases (max ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2))) ((x + 1 / 3) * (x - 1 / 3)) with h6 h6
    · -- Assume max (max A B) C = max A B
      linarith [h4]
    · -- Assume max (max A B) C = C
      nlinarith [h3]
  cases' max_cases (max (max ((x + 1) * (x - 1)) ((x + 1 / 2) * (x - 1 / 2))) ((x + 1 / 3) * (x - 1 / 3))) ((x + 1 / 4) * (x - 1 / 4)) with h6 h6
  · -- Assume the max is the max of A, B, C
    linarith [h5]
  · -- Assume the max is D
    linarith [h6]