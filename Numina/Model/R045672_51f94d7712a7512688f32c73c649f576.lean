import Mathlib

theorem algebra_169431 (p4 : ℝ) (h₀ : p4 ∈ Set.Icc 0 1) (h₁ : 0.1 + 0.2 + 0.4 + p4 + 0.1 = 1) :
    p4 = 0.2 := by
  have h2 : p4 = 0.2 := by
    ring_nf at h₁ ⊢
    linarith
  exact h2