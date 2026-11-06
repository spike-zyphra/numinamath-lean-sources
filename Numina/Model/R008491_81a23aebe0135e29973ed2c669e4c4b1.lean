import Mathlib

theorem number_theory_14824 (s : Finset ℕ) (hs : s = {n ∈ Finset.range 100 | n % 11 = 4 ∧ n % 7 = 1}) : ∑x in s, x = 107 := by 
  rw [hs]
  native_decide