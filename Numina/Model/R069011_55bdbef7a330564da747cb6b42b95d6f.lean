import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189972 (x : ℝ) (hx : x^2 - x - 12 ≥ 0) :
    sqrt (x^2 - x - 12) < x ↔ x ∈ Ici 4 := by
  constructor
  · -- Forward implication: sqrt (x^2 - x - 12) < x → x ∈ Ici 4
    intro h
    have h3 : x > 0 := by linarith [h, show sqrt (x^2 - x - 12) ≥ 0 by positivity]
    have h4 : x ≥ 4 := by 
      nlinarith [Real.sqrt_nonneg (x^2 - x - 12), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 - x - 12 by linarith), sq_nonneg (sqrt (x^2 - x - 12) - x), sq_nonneg (x - 4)]
    exact h4
  · -- Backward implication: x ∈ Ici 4 → sqrt (x^2 - x - 12) < x
    intro h
    have h5 : x ≥ 4 := h
    have h6 : x > 0 := by linarith
    have h7 : sqrt (x^2 - x - 12) < x := by
      nlinarith [Real.sqrt_nonneg (x^2 - x - 12), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 - x - 12 by nlinarith [sq_nonneg (x - 4), sq_nonneg (x + 3)]), sq_nonneg (sqrt (x^2 - x - 12) - x), sq_nonneg (x - 4)]
    exact h7