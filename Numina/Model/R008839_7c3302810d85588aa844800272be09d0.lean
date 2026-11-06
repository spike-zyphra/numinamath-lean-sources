import Mathlib

theorem number_theory_103963 (n : ℕ) (hn : 4 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 (2 * n - 1)) (hS1 : S.card = n) :
    ∃ T ⊆ S, ∑ t ∈ T, t ≡ 0 [ZMOD 2 * n] := by
  use ∅
  constructor
  · 
    simp
  · 
    simp [Int.ModEq]