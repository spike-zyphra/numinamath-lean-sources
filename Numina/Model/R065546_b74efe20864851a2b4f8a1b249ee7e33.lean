import Mathlib

theorem number_theory_123986 (a : Fin 2008 → ℤ) :
    ∃ b : Finset (Fin 2008), ∑ i ∈ b, a i ≡ 0 [ZMOD 2008] := by
  use ∅
  simp [Int.ModEq, Finset.sum_empty]