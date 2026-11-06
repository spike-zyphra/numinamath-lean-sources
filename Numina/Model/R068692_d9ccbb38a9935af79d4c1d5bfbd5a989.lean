import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_75333 (x : ℝ) (hx : x^2 - 5 * x + 6 < 0) :
    20 < (x^2 + 5 * x + 6) ∧ (x^2 + 5 * x + 6) < 30 := by
  have h1 : 2 < x := by
    nlinarith

  have h2 : x < 3 := by 
    nlinarith
  
  have h3 : 20 < (x^2 + 5 * x + 6) := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]

  have h4 : (x^2 + 5 * x + 6) < 30 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]

  constructor
  · exact h3
  · exact h4