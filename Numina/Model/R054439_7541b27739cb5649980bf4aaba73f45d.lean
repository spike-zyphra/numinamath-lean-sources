import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_313119 (f : ℝ → ℝ) (k : ℝ)
  (h₀ : ∀ x ∈ Icc 0 1, f x = k * (x ^ 2 - x + 1) - x ^ 4 * (1 - x) ^ 4)
  (h₁ : ∀ x ∈ Icc 0 1, f x ≥ 0) :
  k ≥ 1 / 192 := by
  have h1 := h₁ (1 / 2) (by norm_num [mem_Icc])
  have h2 := h₀ (1 / 2) (by norm_num [mem_Icc])
  norm_num [h2] at h1 
  linarith