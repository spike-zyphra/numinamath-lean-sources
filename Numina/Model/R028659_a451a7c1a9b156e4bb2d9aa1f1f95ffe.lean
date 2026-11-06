import Mathlib

theorem number_theory_139165 (a : Fin 2008 → ℤ) :
    ∃ s : Finset (Fin 2008), ∑ i ∈ s, a i ≡ 0 [ZMOD 2008] := by 
  use ∅
  simp [Int.ModEq, Finset.sum_empty]