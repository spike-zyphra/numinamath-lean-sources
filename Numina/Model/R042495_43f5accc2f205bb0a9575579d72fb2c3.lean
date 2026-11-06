import Mathlib

open Real Set
open scoped Topology

theorem inequalities_145220 (x : ℝ) (hx : x ∈ Icc 0 1) :
    x * (1 - x) ≤ 1 / 4 := by
  rcases hx with ⟨hx0, hx1⟩
  have h : x * (1 - x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  linarith