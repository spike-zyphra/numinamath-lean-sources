import Mathlib

open Real
open scoped BigOperators

theorem inequalities_69269 : ∑ i ∈ Finset.range 2015, (1 / (i + 1)^3 : ℝ) < 5 / 4 := by
  norm_num
  <;> try { linarith }