import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_79383 {P : ℕ → ℝ → ℝ}
  (hP : ∀ n, P n = λ x => x^(n + 2) - 2 * x + 1)
  (c : ℕ → ℝ)
  (hc : ∀ n, ∃! x, x ∈ Set.Ioo 0 1 ∧ P n x = 0 ∧ c n = x) :
  Tendsto c atTop (𝓝 (1 / 2)) := by 
  have h0 := hc 0
  rcases h0 with ⟨x0, ⟨hx01, ⟨hPx0, hcx0⟩⟩, hx0uq⟩

  rw [hP 0] at hPx0
  simp at hPx0
  rcases hx01 with ⟨hx01l, hx01r⟩

  nlinarith