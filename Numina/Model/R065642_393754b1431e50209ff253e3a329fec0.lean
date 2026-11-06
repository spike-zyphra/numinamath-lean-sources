import Mathlib

theorem number_theory_113217 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i j, i < j → a i ≥ a j) (hsum : ∑ i, a i = 1)
    (ha' : ∀ i, 0 ≤ a i) :
    ∃ k : Fin n → ℕ, (∀ i j, i < j → k i ≥ k j) ∧
    (∀ i, 0 ≤ k i) ∧ (∑ i, a i * k i = 1) := by 
  use (λ _ => 1)
  constructor
  · -- Show that ∀ i j, i < j → (i => 1) ≥ (j => 1)
    intro i j h
    all_goals simp
  constructor
  · -- Show that ∀ i, 0 ≤ k i
    intro i
    simp
  · -- Show that ∑ i, a i * k i = 1
    have h1 : ∑ i, a i * (1 : ℕ) = ∑ i, a i := by
      simp [Finset.sum_congr, mul_one]
    rw [h1]
    exact hsum