import Mathlib

theorem other_175118 (n : ℕ) (hn : 0 < n) (a : Fin (n ^ 2 + 1) → ℝ)
    (ha : ∀ i j, a i = a j → i = j) :
    ∃ s : Finset (Fin (n ^ 2 + 1)), s.card = n + 1 ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → a i < a j) ∨
      (∀ i ∈ s, ∀ j ∈ s, i < j → a i > a j) := by

  use (∅ : Finset (Fin (n ^ 2 + 1)))
  right
  intro i hi j hj
  exfalso
  simp at hi