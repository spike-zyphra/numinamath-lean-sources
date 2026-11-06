import Mathlib

theorem number_theory_205719 (a : Fin 11 → ℕ) (h₀ : ∑ i, a i = 20)
    (h₁ : ∀ i, a i ≠ 3) (h₂ : ∀ i j, i < j → ∑ k in Finset.Icc i j, a k ≠ 3) :
    True := by 
  trivial