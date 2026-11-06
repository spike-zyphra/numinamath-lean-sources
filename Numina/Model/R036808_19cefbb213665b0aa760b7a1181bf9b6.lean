import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_245475 (a b : ℝ) (ha : a + b - 2 ≥ 0) (hb : b - a - 1 ≤ 0) (h : a ≤ 1) :
    (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by

  by_cases h1 : 2 * a + b > 0
  · -- If the denominator is positive, then we can multiply both sides
    have h2 : a + 2 * b ≤ 7 / 5 * (2 * a + b) := by
      nlinarith

    have h3 : (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    linarith

  · -- Denominator is non-positive
    have h2 : 2 * a + b ≤ 0 := by linarith
    have h2a : a + b ≥ 2 := by linarith
    have h2b : b - a ≤ 1 := by linarith
    have h3 : a ≤ 1 := h
    nlinarith