import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_116706
  (x : ℕ → ℝ)
  (a : ℝ)
  (h : Tendsto x atTop (𝓝 a)) :
  (∀ ε > 0, ∃ n, ∀ m, n ≤ m → |x m - a| < ε) ∧
  ¬∃ ε > 0, ∃ n, ∀ m, n ≤ m → |x m - a| ≥ ε := by
  have h1 : ∀ ε > 0, ∃ n, ∀ m, n ≤ m → |x m - a| < ε := by
    rw [Metric.tendsto_atTop] at h
    simpa using h
  have h2 : ¬∃ ε > 0, ∃ n, ∀ m, n ≤ m → |x m - a| ≥ ε := by
    rintro ⟨ε, hε, ⟨n, hn⟩⟩
    have h' : ∀ ε > 0, ∃ N, ∀ m, N ≤ m → |x m - a| < ε := by
      rw [Metric.tendsto_atTop] at h 
      simpa using h
    have h1' := h' ε hε
    rcases h1' with ⟨N, hN⟩
    have h_contra := hn (max n N) (by simp [le_max_right])
    have h_contra2 := hN (max n N) (by simp [le_max_left])
    linarith [abs_nonneg (x (max n N) - a), h_contra, h_contra2]
  exact ⟨h1, h2⟩