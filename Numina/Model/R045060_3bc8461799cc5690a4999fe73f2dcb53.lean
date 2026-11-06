import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_147202 (f : ℂ → ℂ)
  (h₀ : ∀ z, f z = ((1 + z) / (1 - z)) ^ 2)
  (h₁ : ∀ z, z ∈ {z | abs z < 1 ∧ z.im > 0}) :
  ∀ w, w ∈ {w | w.im > 0} ↔ ∃ z, f z = w := by
  have h2 := h₁ 0
  norm_num [Complex.abs] at h2
  all_goals try tauto