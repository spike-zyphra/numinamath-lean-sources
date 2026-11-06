import Mathlib

theorem number_theory_277129 (a : ℕ) (h : a > 0) (n : ℕ) (hn : n > 0)
    (a : ℕ → ℕ → ℕ)
    (h₀ : ∀ i j, a i j = a i 0 ^ 2 ∨ a i j = a i 0 + 1)
    (h₁ : ∀ i, i > 0 → ∀ j, a i j ≠ a i (j - 1)) :
    ∀ i, i > 0 → ∀ j, a i j ≠ a i (j - 1) := by 
  intro i hi j
  apply h₁ i hi j