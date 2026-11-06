import Mathlib

open Real Set
open scoped BigOperators

theorem other_277644 {α : ℝ} (hα : α = arccos 0.98) :
    let g := 10
    let m := 75
    let R := 1
    let r := 75 / 100
    let a := sqrt ((1 - cos α) / 2) * g
    a = sqrt ((1 - cos α) / 2) * g := by 
  rfl