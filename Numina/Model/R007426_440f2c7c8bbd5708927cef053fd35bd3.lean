import Mathlib

theorem algebra_14137 (S : Finset ℕ) (hs : S = {n ∈ Finset.range 101 | 0 < n ∧ (5 ∣ n ∨ 7 ∣ n) ∧ ¬(5 ∣ n ∧ 7 ∣ n)}) :
  S.card = 30 := by 
  rw [hs]
  native_decide