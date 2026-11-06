import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_178778 (x : ℝ) (hx : x > 0) :
    x > log x := by
  have h1 : log x < x := by
    have h2 : log x ≤ x - 1 := by
      linarith [Real.log_le_sub_one_of_pos hx]
    have h7 : x - 1 < (x : ℝ) := by linarith
    linarith
  linarith