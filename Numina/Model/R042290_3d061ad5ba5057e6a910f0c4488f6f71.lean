import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_118438 :
  ∃ a b : ℕ → ℝ, ∃ x y : ℝ, 
    x ≠ y ∧ 
    Tendsto (λ n => a n + b n) atTop (𝓝 2) ∧
    Tendsto a atTop (𝓝 x) ∧
    Tendsto b atTop (𝓝 y) := by
  use (fun (_ : ℕ) => (0 : ℝ)), (fun (_ : ℕ) => (2 : ℝ))
  use (0 : ℝ), (2 : ℝ)
  constructor
  · -- Show x ≠ y
    norm_num
  constructor
  · -- Show Tendsto (fun n => a n + b n) atTop (𝓝 2)
    have h2 : (λ n => ((fun (_ : ℕ) => (0 : ℝ)) n + (fun (_ : ℕ) => (2 : ℝ)) n)) = (λ _ => (2 : ℝ)) := by
      funext n
      simp
    rw [h2]
    apply tendsto_const_nhds
  constructor
  · -- Show Tendsto a atTop (𝓝 x)
    apply tendsto_const_nhds
  · -- Show Tendsto b atTop (𝓝 y)
    apply tendsto_const_nhds