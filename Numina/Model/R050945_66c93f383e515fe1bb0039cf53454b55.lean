import Mathlib

theorem algebra_297955 (a : ℝ) (ha : 0 < a) (x y z : ℝ)
    (h1 : x + y + z = a) (h2 : x^2 + y^2 + z^2 = (1 / 2) * a^2) :
    0 ≤ x ∧ x ≤ (2 / 3) * a ∧ 0 ≤ y ∧ y ≤ (2 / 3) * a ∧ 0 ≤ z ∧ z ≤ (2 / 3) * a := by
  constructor
  · -- Show that 0 ≤ x
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - a), sq_nonneg (x^2 + y^2 + z^2 - (1 / 2) * a^2)]
  constructor
  · -- Show that x ≤ (2 / 3) * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - a), sq_nonneg (x^2 + y^2 + z^2 - (1 / 2) * a^2)]
  constructor
  · -- Show that 0 ≤ y
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - a), sq_nonneg (x^2 + y^2 + z^2 - (1 / 2) * a^2)]
  constructor
  · -- Show that y ≤ (2 / 3) * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - a), sq_nonneg (x^2 + y^2 + z^2 - (1 / 2) * a^2)]
  constructor
  · -- Show that 0 ≤ z
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - a), sq_nonneg (x^2 + y^2 + z^2 - (1 / 2) * a^2)]
  · -- Show that z ≤ (2 / 3) * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - a), sq_nonneg (x^2 + y^2 + z^2 - (1 / 2) * a^2)]