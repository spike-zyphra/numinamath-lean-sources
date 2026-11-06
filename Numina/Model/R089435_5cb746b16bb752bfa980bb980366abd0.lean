import Mathlib

theorem algebra_19938 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999} = 900 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999} = Finset.Icc 100 999 := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide