import Mathlib

theorem inequalities_602731 (a : ℝ) (ha : 0 < a) (x y z : ℝ)
    (h₀ : x + y + z = a) (h₁ : x^2 + y^2 + z^2 ≤ (a^2) / 2) :
    0 ≤ x ∧ x ≤ (2 * a) / 3 ∧ 0 ≤ y ∧ y ≤ (2 * a) / 3 ∧ 0 ≤ z ∧ z ≤ (2 * a) / 3 := by
  constructor
  · -- Prove that 0 ≤ x
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - a), mul_pos ha ha]
  constructor
  · -- Prove that x ≤ 2*a/3
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - a), mul_pos ha ha]
  constructor
  · -- Prove that 0 ≤ y
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - a), mul_pos ha ha]
  constructor
  · -- Prove that y ≤ 2*a/3
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - a), mul_pos ha ha]
  constructor
  · -- Prove that 0 ≤ z
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - a), mul_pos ha ha]
  · -- Prove that z ≤ 2*a/3
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - a), mul_pos ha ha]