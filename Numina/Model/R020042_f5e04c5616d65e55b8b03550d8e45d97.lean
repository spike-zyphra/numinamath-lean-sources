import Mathlib

theorem number_theory_116765 (a b : ℤ) (W : ℤ → ℤ) (hW : ∀ x, W x = x ^ 2 + a * x + b)
    (hW' : ∀ p, Prime p → ∃ k, p ∣ W k ∧ p ∣ W (k + 1)) :
    ∃ m, ∀ x, m ∣ W x := by 
  use 1
  intro x
  simp [hW]