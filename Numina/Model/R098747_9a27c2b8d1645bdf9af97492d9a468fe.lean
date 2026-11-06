import Mathlib

theorem number_theory_322826 (n : ℕ) (hn : 4 ≤ n) (a : Fin n → ℕ)
    (ha : ∀ i j, a i = a j → i = j) (ha1 : ∀ i, 0 < a i ∧ a i < 2 * n) :
    ∃ s : Finset (Fin n), ∑ i ∈ s, a i ≡ 0 [ZMOD 2 * n] := by 
  use ∅ 
  simp [Int.ModEq, Finset.sum_eq_zero]