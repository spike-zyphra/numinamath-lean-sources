import Mathlib

theorem number_theory_239021 (n : ℕ) (hn : n > 10) (a : Fin n → ℕ)
    (ha : ∑ i, a i = 20) (h : ∀ i, a i ≠ 3) (h' : ∀ i j, i ≤ j → ∑ k in Finset.Icc i j, a k ≠ 3) :
    True := by 
  trivial