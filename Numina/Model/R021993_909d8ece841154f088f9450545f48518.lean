import Mathlib

open Finset Real

theorem inequalities_314675 {n : ℕ} (hn : n ≥ 4) (a : Fin n → Fin n → Bool)
    (ha : ∀ i j, a i j ↔ a j i) (h : ∀ i, a i i = False)
    (h' : ∀ i j k l, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l →
      (a i j ∧ a i k ∧ a i l ∧ a j k ∧ a j l ∧ a k l)) :
    ∑ i, (Nat.card {j | a i j})^3 ≥ 0 := by
  have h1 : 0 ≤ ∑ i : Fin n, (Nat.card {j | a i j})^3 := by
    apply Finset.sum_nonneg
    intro i hi
    have h2 : (Nat.card {j | a i j})^3 ≥ 0 := by
      have h4 : Nat.card {j | a i j} ≥ 0 := by
        omega
      positivity
    simpa using h2
  linarith