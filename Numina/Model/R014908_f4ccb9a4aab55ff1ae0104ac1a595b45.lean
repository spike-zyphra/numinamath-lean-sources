import Mathlib

theorem algebra_600072 (a b c : ℝ) (ha : a + b + c = 2) (hb : a^2 + 2 * b^2 + 3 * c^2 = 4) :
    2 / 11 ≤ a ∧ a ≤ 2 := by
  have h1 : c = 2 - a - b := by
    linarith
  rw [h1] at hb
  constructor
  · -- Prove that 2/11 ≤ a
    nlinarith [sq_nonneg (b - 12 / 11), sq_nonneg ((2 - a - b) - 8 / 11), sq_nonneg (a - 2 / 11), sq_nonneg (a - 2), sq_nonneg (b - 12 / 11), sq_nonneg ((2 - a - b) - 8 / 11)]
  · -- Prove that a ≤ 2
    nlinarith [sq_nonneg (b), sq_nonneg ((2 - a - b)), sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg ((2 - a - b)), sq_nonneg (a - 2)]