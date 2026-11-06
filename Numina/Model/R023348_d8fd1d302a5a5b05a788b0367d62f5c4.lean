import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_184173 (x : ℝ) (hx : x ≠ 0) : exp x > 1 + x := by
  have h : x + 1 < exp x := by
    apply Real.add_one_lt_exp
    exact hx
  linarith [h]