import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_155037 :
  Tendsto (λ x => (3 / (x + 5))) atTop (𝓝 0) := by
  -- To prove Tendsto (λ x => (3 / (x + 5))) atTop (𝓝 0), we need to show
  -- for each neighborhood U of 0, for all x large enough, 3/(x + 5) ∈ U
  -- Let's compute N such that when x > N, |3/(x + 5)| < ε
  -- Let ε > 0. We find N such that when x > N, 3/(x + 5) < ε
  -- Solving: 3/(x + 5) < ε
  -- x + 5 > 3/ε
  -- x > 3/ε - 5
  -- Take N = ⌊3/ε - 5⌋ + 1
  -- Then x > N implies 3/(x + 5) < ε
  -- For Lean, this can be expressed by showing Tendsto directly
  apply by_contra
  intro h
  -- Lean can solve the contradiction automatically
  simpa using h