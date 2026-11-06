import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327156 (f : ℝ → ℝ) (k : ℝ)
  (h₀ : ∀ x ∈ Icc 0 1, f x = k * (x^2 - x + 1) - x^3 * (1 - x)^3)
  (h₁ : ∀ x ∈ Icc 0 1, f x ≥ 0) :
  k ≥ 1 / 48 := by
    by_contra h
    push_neg at h
    have h2 : f (1 / 2) ≥ 0 := h₁ (1 / 2) (by norm_num)
    have eq : f (1 / 2) = k * ( (1 / 2)^2 - 1 / 2 + 1 ) - (1 / 2)^3 * (1 - (1 / 2))^3 := by
      apply h₀ (1 / 2)
      exact (by norm_num)
    rw [eq] at h2
    norm_num at h2
    linarith