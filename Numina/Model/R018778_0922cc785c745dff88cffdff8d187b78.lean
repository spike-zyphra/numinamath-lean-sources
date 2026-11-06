import Mathlib

theorem algebra_312882 (a : ℝ) (ha : 0 < a) (x y z : ℝ)
    (hsum : x + y + z = a) (hsumsq : x^2 + y^2 + z^2 = a^2 / 2) :
    0 ≤ x ∧ x ≤ 2 / 3 * a ∧ 0 ≤ y ∧ y ≤ 2 / 3 * a ∧ 0 ≤ z ∧ z ≤ 2 / 3 * a := by
  constructor
  · -- Show 0 ≤ x
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                hsum, hsumsq, sq_pos_of_pos ha]
  constructor
  · -- Show x ≤ 2 / 3 * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                hsum, hsumsq, sq_pos_of_pos ha]
  constructor
  · -- Show 0 ≤ y
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                hsum, hsumsq, sq_pos_of_pos ha]
  constructor
  · -- Show y ≤ 2 / 3 * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                hsum, hsumsq, sq_pos_of_pos ha]
  constructor
  · -- Show 0 ≤ z
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                hsum, hsumsq, sq_pos_of_pos ha]
  · -- Show z ≤ 2 / 3 * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                hsum, hsumsq, sq_pos_of_pos ha]