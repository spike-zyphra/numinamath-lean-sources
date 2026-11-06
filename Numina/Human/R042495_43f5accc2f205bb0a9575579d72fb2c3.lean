import Mathlib

open Real Set
open scoped Topology

theorem inequalities_145220 (x : ℝ) (hx : x ∈ Icc 0 1) :
    x * (1 - x) ≤ 1 / 4 := by
  have h1 : 0 ≤ x := hx.1
  have h2 : x ≤ 1 := hx.2
  have h3 : (x - 1 / 2) ^ 2 ≥ 0 := by
    exact sq_nonneg (x - 1 / 2)
  linarith