import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_185611 {a : ℝ} (ha : a > 0) :
    let x := ∫ x in (0)..a, x * sqrt (a - x) / (a * (a - x))
    let y := ∫ y in (0)..a, y * sqrt (a - y) / (a * (a - y))
    x = y := by 
  simp 
  all_goals 
    norm_num
    <;> try { ring_nf <;> norm_num }