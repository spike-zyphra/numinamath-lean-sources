import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_194867 (b : ℝ) :
  (∀ x y : ℝ, (x^2 + y^2)^2 ≤ b * (x^4 + y^4)) ↔ b ≥ 2 := by
  constructor
  · -- Assume that for all x and y, (x^2 + y^2)^2 ≤ b * (x^4 + y^4), prove b ≥ 2
    intro h
    have h1 := h 1 1
    norm_num at h1
    nlinarith
  · -- Assume b ≥ 2, prove ∀ x y, (x^2 + y^2)^2 ≤ b * (x^4 + y^4)
    intro hb x y
    have h1 : (x^2 + y^2)^2 ≤ 2 * (x^4 + y^4) := by
      nlinarith [sq_nonneg (x^2 - y^2)]
    have h2 : 0 ≤ (b - 2) := by linarith
    nlinarith [sq_nonneg (x^2 - y^2), hb, h1, h2, show x^4 + y^4 ≥ 0 by positivity]