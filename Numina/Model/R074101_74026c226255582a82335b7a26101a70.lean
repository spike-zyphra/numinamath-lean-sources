import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_158741 {g : ℝ → ℝ} (hg : g = λ y => if y ∈ Ioo (-1) 1 then (1 / (Real.pi * Real.sqrt (1 - y^2))) else 0) :
    ∀ y, g y = if y ∈ Ioo (-1) 1 then (1 / (Real.pi * Real.sqrt (1 - y^2))) else 0 := by
  intro y
  rw [hg]
  all_goals norm_num
  <;> try { simp }
  <;> try { ring }