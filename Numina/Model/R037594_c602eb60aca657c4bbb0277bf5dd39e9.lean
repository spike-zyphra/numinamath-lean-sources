import Mathlib

theorem number_theory_323462 (n : ℕ) (hn : 4 ≤ n) (a : Fin n → ℕ)
    (ha : ∀ i j, a i = a j → i = j) (ha1 : ∀ i, 0 < a i ∧ a i < 2 * n) :
    ∃ t : Finset (Fin n), 2 * n ∣ ∑ i ∈ t, a i := by 
  use ∅
  simp