import Mathlib

theorem number_theory_237340 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 1000 ∧ x % 11 = x % 12} = 87 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 1000 ∧ x % 11 = x % 12} = Finset.filter (fun x => x % 11 = x % 12) (Finset.Icc 1 1000) := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide