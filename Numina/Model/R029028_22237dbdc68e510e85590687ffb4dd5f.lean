import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_123120
  (f : ℝ → ℝ)
  (h₀ : ∀ x, 0 ≤ x ∧ x ≤ 1 → 0 < f x)
  (h₁ : f 1 = 1)
  (h₂ : ∀ x y, x + y ≤ 1 → f (x + y) ≥ f x + f y) :
  (∀ x, 0 ≤ x ∧ x ≤ 1 → f x ≤ 2 * x) ∧
  (∀ c, (∀ x, 0 ≤ x ∧ x ≤ 1 → f x ≤ c * x) → c ≥ 2) := by
  have h3 : 0 < f 0 := by
    specialize h₀ 0 (by norm_num)
    simpa using h₀
  have h4 : f 0 ≥ f 0 + f 0 := by
    specialize h₂ 0 0 (by norm_num)
    simpa using h₂
  have h5 : f 0 ≤ 0 := by linarith
  linarith