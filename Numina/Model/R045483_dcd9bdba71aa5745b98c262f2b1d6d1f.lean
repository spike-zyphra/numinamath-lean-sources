import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_107794
  (f g : ℝ → ℝ)
  (h₀ : ∀ x y, x < y → f x < f y)
  (h₁ : ∀ x y, x < y → g x < g y) :
  (∀ a b, b ∈ Set.Icc (f (a - 0)) (f (a + 0)) →
    ∀ x, ∫ t in (a)..x, f t ≥ b * (x - a)) ∧
  (∀ a, ∃ b, b ∈ Set.Icc (f (a - 0)) (f (a + 0)) ∧
    b ∈ Set.Icc (g (a - 0)) (g (a + 0))) →
  (∀ a b, a < b → ∫ t in (a)..b, f t = ∫ t in (a)..b, g t) := by
  intro h
  intro a b hab
  have h3 : ∀ a, ∃ b, b ∈ Set.Icc (f (a - 0)) (f (a + 0)) ∧ b ∈ Set.Icc (g (a - 0)) (g (a + 0)) := h.2
  have h_eq3 : ∀ x : ℝ, f x = g x := by
    intro x
    have h4'' := h3 x
    rcases h4'' with ⟨c'', hc1'', hc2''⟩
    have hc3'' : c'' = f x := by
      have hc11'' : c'' ∈ Set.Icc (f (x - 0)) (f (x + 0)) := hc1''
      have h7 : x - 0 = (x : ℝ) := by ring
      have h8 : x + 0 = (x : ℝ) := by ring
      rw [h7, h8] at hc11''
      simp at hc11'' ⊢
      linarith
    have hc4'' : c'' = g x := by
      have hc22'' : c'' ∈ Set.Icc (g (x - 0)) (g (x + 0)) := hc2''
      have h7 : x - 0 = (x : ℝ) := by ring
      have h8 : x + 0 = (x : ℝ) := by ring
      rw [h7, h8] at hc22''
      simp at hc22'' ⊢
      linarith
    linarith
  have h_eq3' : ∀ t : ℝ, f t = g t := h_eq3
  simp_all
  all_goals
    try nlinarith