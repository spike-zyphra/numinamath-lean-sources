import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_228046
  (a : ℕ → ℝ)
  (h : ∃ L, Tendsto (λ n => a n) atTop (𝓝 L)) :
  ∃! L, Tendsto (λ n => a n) atTop (𝓝 L) := by
  rcases h with ⟨L, hL⟩
  use L
  constructor
  · exact hL
  · -- Show that any other limit must be equal to L
    intro M hM
    have h1 : Tendsto (λ n => a n) atTop (𝓝 L) := hL
    have h2 : Tendsto (λ n => a n) atTop (𝓝 M) := hM
    have h3 : M = L := by 
      apply tendsto_nhds_unique h2 h1 
    linarith