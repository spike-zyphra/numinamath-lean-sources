import Mathlib

theorem algebra_19944 : Set.ncard {x : ℕ | x ∈ Finset.Icc 36 93} = 58 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 36 93} = Finset.Icc 36 93 := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  all_goals native_decide