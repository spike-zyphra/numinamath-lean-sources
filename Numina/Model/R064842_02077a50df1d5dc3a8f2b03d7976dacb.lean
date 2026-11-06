import Mathlib

theorem number_theory_10043 :
  ((Finset.Icc 1 1000).filter
    fun m =>
      Nat.Coprime (m + 4) (m ^ 2 + 7)).card = 957 := by
  native_decide