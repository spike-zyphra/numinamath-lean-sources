import Mathlib

theorem algebra_803 : ⌊(10 * (2000 ^ 2001 + 2001 ^ 2002 : ℝ) / (2000 ^ 2000 + 2001 ^ 2001))⌋ = 20009 := by
  norm_num [Int.floor_eq_iff]
  <;> norm_num
  <;> try linarith
  <;> try omega