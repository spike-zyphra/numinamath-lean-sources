import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_116842
  (x : ℕ → ℝ)
  (a : ℝ)
  (h : ∀ ε > 0, ∃ k, ∀ n, k < n → |x n - a| < ε) :
  ∃ L, Tendsto x atTop (𝓝 L) ∧ L = a := by
  use a
  constructor
  · -- Tendsto x atTop (𝓝 a)
    have h2 : Tendsto x atTop (𝓝 a) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      have h3 : ∃ k, ∀ n, k < n → |x n - a| < ε := h ε (show ε > 0 by linarith)
      rcases h3 with ⟨k, hk⟩
      use k + 1
      intro n hn
      have h4 : dist (x n) a = |x n - a| := by
        simp [dist]
      have h5 : k < n := by
        omega
      have h7 : |x n - a| < ε := by
        apply hk n
        exact h5
      rw [h4]
      linarith
    exact h2
  · -- Show L = a
    rfl