import Mathlib

theorem number_theory_36827 {f : ℕ → ℕ} (hf : ∀ a b, 0 < a → 0 < b → 2 * f (a * b) = (b + 1) * f a + (a + 1) * f b)
    (hf' : ∃ x, 0 < x ∧ f x ≠ 0) :
    ∀ p, Nat.Prime p → ∃ q, Nat.Prime q ∧ ∃ x : Finset ℕ, ∃ m, ∀ i ∈ x, 0 < i ∧
      f (q ^ p) / f q = ∏ i ∈ x, (p * i + 1) * p ^ m ∧ ∀ i ∈ x, Nat.Prime (p * i + 1) := by

  intro p hp
  use p
  constructor
  exact hp

  use ∅
  use 0
  intro i hi
  exfalso
  simp at hi