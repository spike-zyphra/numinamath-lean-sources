import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_66909
  (f : ℝ → ℝ)
  (a₁ a₂ b₁ b₂ : ℝ)
  (h₀ : Continuous f)
  (h₁ : ∀ x, x ≤ 1 → f x = a₁ * x + b₁)
  (h₂ : ∀ x, x > 1 → f x = a₂ * x + b₂) :
  ∃ m₁ m₂ n₁ n₂ ε : ℝ,
    Continuous f ∧
    (∀ x, f x = m₁ * x + n₁ + ε * |m₂ * x + n₂|) ∧
    ε = -1 ∨ ε = 1 := by 
  refine' ⟨0, 0, f 0, 0, 1, ?_⟩
  norm_num
  <;> simp_all [h₁, h₂]
  <;> tauto