import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem number_theory_44492 (α : ℕ → ℕ)
  (hα : ∀ a, Odd (α a) ∧ α a ∣ a ∧ ∀ d, Odd d → d ∣ a → d ≤ α a) :
  ∃ L, Tendsto (λ b => (∑ a in (Icc 1 b), (α a : ℝ) / a) / b) atTop (𝓝 L) ↔ L = 1 := by

  have h1 := hα 0
  rcases h1 with ⟨h1_odd, h1_dvd, h1_greatest⟩
  have h2 := h1_greatest (α 0 + 2)
  have h3 : Odd (α 0 + 2) := by
    have h4 : Odd (α 0) := h1_odd
    rcases h4 with ⟨k, hk⟩
    use k + 1
    linarith
  have h4 : (α 0 + 2) ∣ 0 := by
    use 0
    simp
  have h5 := h2 h3 h4
  omega