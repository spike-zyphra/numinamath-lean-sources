import Mathlib

theorem algebra_172342 {a c : ℝ} (ha : a ≠ 0) (h1 : -4 ≤ a * 1 ^ 2 - c ∧ a * 1 ^ 2 - c ≤ -1)
    (h2 : -1 ≤ a * 2 ^ 2 - c ∧ a * 2 ^ 2 - c ≤ 5) :
    -1 ≤ a * 3 ^ 2 - c ∧ a * 3 ^ 2 - c ≤ 20 := by
  have h11 : -4 ≤ a * 1 ^ 2 - c := h1.1
  have h12 : a * 1 ^ 2 - c ≤ -1 := h1.2
  have h21 : -1 ≤ a * 2 ^ 2 - c := h2.1
  have h22 : a * 2 ^ 2 - c ≤ 5 := h2.2
  constructor
  · -- Show the lower bound
    nlinarith [sq_nonneg (a * 1 ^ 2 - c), sq_nonneg (a * 2 ^ 2 - c), sq_nonneg (a - 2)]
  · -- Show the upper bound
    nlinarith [sq_nonneg (a * 1 ^ 2 - c), sq_nonneg (a * 2 ^ 2 - c), sq_nonneg (a - 2)]