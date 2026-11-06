import Mathlib

open Finset

theorem algebra_137332 (x : ℕ → ℝ)
    (h₁ : ∑ i ∈ range 30, (i + 20)^3 * x i = 13)
    (h₂ : ∑ i ∈ range 30, (i + 21)^3 * x i = 1)
    (h₃ : ∑ i ∈ range 30, (i + 22)^3 * x i = 19) :
    ∑ i ∈ range 30, (i + 21) * x i = 5 := by

  norm_num [Finset.sum_range_succ] at h₁ h₂ h₃ ⊢
  linarith