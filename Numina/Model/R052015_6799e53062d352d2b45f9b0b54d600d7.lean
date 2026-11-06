import Mathlib

theorem algebra_309221 (a b : ℝ) (h : a^2 + b^2 = a + b) :
    0 ≤ a + b ∧ a + b ≤ 2 := by
  have h1 : (a - b) ^ 2 ≥ 0 := by
    exact sq_nonneg (a - b)
  have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  rw [h] at h2
  have h3 : (a + b) * (a + b - 2) ≤ 0 := by
    nlinarith
  constructor
  · -- First part: proving 0 ≤ a + b
    nlinarith
  · -- Second part: proving a + b ≤ 2
    nlinarith