import Mathlib

open Finset

theorem number_theory_158950 {k : ℕ} (a : ℕ → ℕ) (ha : ∀ i ∈ Icc 0 k, a i ≤ 9)
    (Q : ℕ → ℕ) (hQ : ∀ n, Q n = ∏ i ∈ Icc 0 k, a i) :
    {n | ∃ m, n = m ∧ Nat.Prime (Q n)}.ncard ≤ 2 * (k + 1) * (k + 2) := by 
  have h1 : ∀ n, Q n = Q 0 := by
    intro n
    have h2 : Q n = ∏ i ∈ Icc 0 k, a i := hQ n
    have h3 : Q 0 = ∏ i ∈ Icc 0 k, a i := hQ 0
    rw [h2, h3]
  have h2 : {n | ∃ m, n = m ∧ Nat.Prime (Q n)} = (∅ : Set ℕ) ∨ {n | ∃ m, n = m ∧ Nat.Prime (Q n)} = (Set.univ : Set ℕ) := by 
    by_cases h3 : Nat.Prime (Q 0)
    · -- If Q 0 is prime, then Q n is prime for all n. 
      have h4 : ∀ n, Nat.Prime (Q n) := by
        intro n
        rw [show Q n = Q 0 by apply h1]
        exact h3
      have h5 : {n | ∃ m, n = m ∧ Nat.Prime (Q n)} = (Set.univ : Set ℕ) := by
        ext n
        simp [h4]
      right
      exact h5
    · -- If Q 0 is not prime, then Q n is not prime for all n.
      have h4 : ∀ n, ¬ Nat.Prime (Q n) := by
        intro n
        rw [show Q n = Q 0 by apply h1]
        exact h3
      have h5 : {n | ∃ m, n = m ∧ Nat.Prime (Q n)} = (∅ : Set ℕ) := by
        ext n
        simp [h4]
      left
      exact h5
  rcases h2 with (h | h)
  · -- If the set is empty.
    rw [h]
    simp
  · -- If the set is the set of all natural numbers.
    rw [h]
    rw [Set.ncard_univ]
    simp at *
    all_goals try { tauto }