import Mathlib

open Nat

theorem other_5072 {n m : ℕ} (hn : n = 0b100011110101) (hm : m = 0b11101001110) :
    n = 0x8f5 ∧ m = 0x74e := by 
  have hn1 : n = 0x8f5 := by
    simp [hn]
  have hm1 : m = 0x74e := by 
    simp [hm]
  exact ⟨hn1, hm1⟩