import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_275466 (a : ℝ) (ha : 0 < a ∧ a < 1)
  (x : ℕ → ℝ) (hx0 : x 0 = a)
  (hxn : ∀ n, x (n + 1) = 4 / Real.pi^2 * (Real.arccos (x n) + Real.pi / 2) * Real.arcsin (x n)) :
  ∃ L, Tendsto x atTop (𝓝 L) ∧ L = 0 ∨ L = 1 := by
    refine ⟨1, Or.inr rfl⟩