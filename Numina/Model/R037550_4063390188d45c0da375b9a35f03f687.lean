import Mathlib

open Real

theorem inequalities_218291 (k : ℝ) :
    (∀ x y z : ℝ, (x^2 + y^2 + z^2)^2 ≤ k * (x^4 + y^4 + z^4)) ↔ k ≥ 3 := by
  constructor
  · -- Assume that ∀ x, y, z, (x^2 + y^2 + z^2)^2 ≤ k * (x^4 + y^4 + z^4), prove k ≥ 3.
    intro h
    have h1 := h 1 1 1
    nlinarith
  · -- Assume k ≥ 3, prove ∀ x, y, z, (x^2 + y^2 + z^2)^2 ≤ k * (x^4 + y^4 + z^4).
    intro hk x y z
    have h1 : (x^2 + y^2 + z^2)^2 ≤ 3 * (x^4 + y^4 + z^4) := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
        sq_nonneg (x^2 + y^2 - z^2), sq_nonneg (x^2 - y^2 + z^2), sq_nonneg (-x^2 + y^2 + z^2)]
    have h2 : k ≥ 3 := by linarith
    have h3 : k * (x^4 + y^4 + z^4) ≥ 3 * (x^4 + y^4 + z^4) := by
      have : k ≥ 3 := h2
      nlinarith
    linarith [h1, h3]