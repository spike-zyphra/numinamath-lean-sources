import Mathlib

theorem other_227920 :
    {x | x ∈ Finset.range 90 ∧ (x % 2 = 0 ∧ x % 3 ≠ 0 ∧ x % 5 ≠ 0)}.ncard = 24 := by 
  have : {x | x ∈ Finset.range 90 ∧ (x % 2 = 0 ∧ x % 3 ≠ 0 ∧ x % 5 ≠ 0)} = Finset.filter (fun x => x % 2 = 0 ∧ x % 3 ≠ 0 ∧ x % 5 ≠ 0) (Finset.range 90) := by 
    ext x 
    simp 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide