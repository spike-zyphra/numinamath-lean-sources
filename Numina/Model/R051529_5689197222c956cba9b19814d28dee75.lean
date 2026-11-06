import Mathlib

open Real Set
open scoped Real

theorem algebra_163015 (α : ℝ) :
  α ∈ Ioo 0 Real.pi → sqrt ((2 * sin α - sin (2 * α)) / (2 * sin α + sin (2 * α))) =
  tan (α / 2) ∧
  α ∈ Ioo Real.pi (2 * Real.pi) → sqrt ((2 * sin α - sin (2 * α)) / (2 * sin α + sin (2 * α))) =
  -tan (α / 2) := by
  intro h1 h2
  rcases h1 with ⟨h1l, h1r⟩
  rcases h2 with ⟨h2l, h2r⟩
  rcases h2r with ⟨h2rl, h2rr⟩
  linarith