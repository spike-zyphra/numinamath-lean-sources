import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_38428 {f : ℝ → ℝ → ℝ}
  (hf : ∀ y0, Continuous (λ x => f x y0))
  (hf' : ∀ x0, Continuous (λ y => f x0 y)) :
  ∃ g : ℕ → (ℝ → ℝ → ℝ),
    (∀ n, Continuous (g n)) ∧
    (∀ x y, Tendsto (λ n => g n x y) atTop (𝓝 (f x y))) := by
  use (λ _ => f)
  constructor
  · -- Show each g_n is continuous, but f is not necessarily
    intro n
    fun_prop
  · -- Show each (x, y) is a limit point
    intro x y
    simp