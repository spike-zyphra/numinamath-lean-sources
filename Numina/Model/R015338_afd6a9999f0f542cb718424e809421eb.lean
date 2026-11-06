import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_28563
  (f g : ℝ → ℝ)
  (h₀ : ∀ a b, a ≤ b → f a ≤ f b)
  (h₁ : ∀ a b, a ≤ b → g a ≤ g b) :
  (∀ a b x, a ≤ b → b ∈ Set.Icc (f (a - 0)) (f (a + 0)) →
    ∫ t in (a)..x, f t ≥ b * (x - a)) ∧
  (∀ a, ∃ b, a ≤ b ∧ b ∈ Set.Icc (f (a - 0)) (f (a + 0)) ∧
    b ∈ Set.Icc (g (a - 0)) (g (a + 0))) →
  (∀ a b, a < b → ∫ t in (a)..b, f t = ∫ t in (a)..b, g t) := by
  aesop