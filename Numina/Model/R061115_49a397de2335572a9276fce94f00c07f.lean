import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_116695
  (x : ℕ → ℝ)
  (a : ℝ)
  (h : Tendsto x atTop (𝓝 a)) :
  ∀ ε > 0, ∃ n, ∀ m, n < m → |x m - a| < ε := by
  -- Rewrite the hypothesis using the definition of tendsto in a metric space
  rw [Metric.tendsto_atTop] at h 
  intro ε hε
  specialize h ε hε 
  rcases h with ⟨n, hn⟩ 
  use n 
  intro m hm 
  have h' : n ≤ m := by linarith 
  specialize hn m h' 
  simpa using hn