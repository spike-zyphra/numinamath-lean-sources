import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_148144 :
  Tendsto (λ x => ((x^3 - 2 * x - 1) * (x + 1)) / (x^4 + 4 * x^2 - 5)) (𝓝[≠] (-1)) (𝓝 0) := by 
  have h1 : Tendsto (λ x => ((x^3 - 2 * x - 1) * (x + 1)) / (x^4 + 4 * x^2 - 5)) (𝓝 (-1)) (𝓝 0) := by
    norm_num [Tendsto]
    <;> norm_num
    all_goals try { aesop }
    all_goals try { tauto }
  have h2 : Tendsto (λ x => ((x^3 - 2 * x - 1) * (x + 1)) / (x^4 + 4 * x^2 - 5) ) (𝓝[≠] (-1)) (𝓝 0) := by 
    have h3 : Tendsto (λ x => ((x^3 - 2 * x - 1) * (x + 1)) / (x^4 + 4 * x^2 - 5) ) (𝓝 (-1)) (𝓝 0) := h1
    have h4 : Tendsto (λ x => ((x^3 - 2 * x - 1) * (x + 1)) / (x^4 + 4 * x^2 - 5) ) (𝓝[≠] (-1)) (𝓝 0) := by 
      have h5 : (𝓝[≠] (-1)) ≤ (𝓝 (-1)) := by 
        apply nhdsWithin_le_nhds
      have h6 : Tendsto (λ x => ((x^3 - 2 * x - 1) * (x + 1)) / (x^4 + 4 * x^2 - 5) ) (𝓝 (-1)) (𝓝 0) := h1
      apply Tendsto.mono_left h6 h5 
    exact h4
  exact h2