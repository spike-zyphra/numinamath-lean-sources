import Mathlib

theorem number_theory_141077 (n : ℕ) (hn : 0 < n) (a : Fin n → ℤ) :
    ∃ s : Finset (Fin n), ∑ i ∈ s, a i ≡ 0 [ZMOD n] := by 
  exact ⟨∅, rfl⟩