import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_228444
  (f : ℝ → ℝ)
  (x₀ : ℝ)
  (h : ∃ L, Tendsto (λ x => f x) (𝓝 x₀) (𝓝 L)) :
  ∃! L, Tendsto (λ x => f x) (𝓝 x₀) (𝓝 L) := by
    rcases h with ⟨L, hL⟩
    use L
    constructor
    · exact hL
    · -- Now we need to prove uniqueness
      intro L' hL'
      have h1 : Tendsto (λ x => f x) (𝓝 x₀) (𝓝 L) := hL
      have h2 : Tendsto (λ x => f x) (𝓝 x₀) (𝓝 L') := hL'
      -- Now apply uniqueness of limits
      have h3 : L' = L := by
        apply tendsto_nhds_unique h2 h1
      linarith