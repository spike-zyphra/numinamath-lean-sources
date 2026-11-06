import Mathlib

theorem number_theory_204139 (k : ℕ) (a : Fin k → ℤ) :
    ∃ t : Finset (Fin k), ∑ i ∈ t, a i ≡ 0 [ZMOD k] := by 
  use ∅
  simp [Int.ModEq]