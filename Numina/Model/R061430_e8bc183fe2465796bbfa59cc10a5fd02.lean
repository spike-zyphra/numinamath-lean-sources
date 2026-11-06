import Mathlib

theorem algebra_3677 {a : ℝ} (ha : a ^ 2 + 1 = a) :
    ∑ i ∈ Finset.range 213, (-1 : ℝ) ^ (213 - i) * a ^ i = 0 := by
  have h1 : a ^ 2 = a - 1 := by linarith
  have h6 : a ^ 2 - a + 1 = 0 := by linarith
  have h7 : (a - 1/2) ^ 2 ≥ 0 := sq_nonneg (a - 1/2)
  nlinarith [sq_nonneg (a - 1 / 2)]