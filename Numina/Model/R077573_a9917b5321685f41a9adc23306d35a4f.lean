import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_228195 (x : ℝ) :
  Tendsto (λ n => x ^ n / Nat.factorial n) atTop (𝓝 0) := by
  have h : ∀ x : ℝ, Tendsto (λ (n : ℕ) => x ^ n / Nat.factorial n) atTop (𝓝 0) := by
    intro x
    exact? -- need import
  specialize h x
  simpa using h