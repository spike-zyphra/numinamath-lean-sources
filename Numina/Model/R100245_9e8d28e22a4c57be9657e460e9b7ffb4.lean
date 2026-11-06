import Mathlib

theorem number_theory_5730 (n : ℕ) (h₀ : n = 20181216) (h₁ : n.primeFactors.card = 5) :
    ∃ p ∈ n.primeFactors, p ∈ Finset.Icc 100 999 := by 
  rw [h₀] at h₁ ⊢
  native_decide