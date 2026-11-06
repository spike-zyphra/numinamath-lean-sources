import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_171299 (x : ℝ) :
  (x^2 + 4 * x + 10)^2 - 7 * (x^2 + 4 * x + 11) + 7 < 0 ↔ x ∈ Ioo (-3) (-1) := by
  constructor
  · -- Forward implication: from inequality to interval
    intro h
    have h1 : (x^2 + 4 * x + 10) ^ 2 - 7 * (x^2 + 4 * x + 11) + 7 < 0 := h
    have h2 : x^2 + 4 * x + 3 < 0 := by
      nlinarith [sq_nonneg (x^2 + 4 * x + 10 - 3.5), sq_nonneg (x + 1.5)]
    constructor
    · -- Show that -3 < x
      nlinarith [h2]
    · -- Show that x < -1
      nlinarith [h2]
  · -- Reverse implication: from interval to inequality
    rintro ⟨h1, h2⟩
    have h3 : x^2 + 4 * x + 3 < 0 := by
      nlinarith
    nlinarith [sq_nonneg (x^2 + 4 * x + 10 - 3.5), sq_nonneg (x + 1.5)]