import Mathlib

theorem algebra_14250 : {x | x ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 x).length = 3 ∧ (Nat.digits 10 x).toFinset = {9, 8, 7}}.ncard = 6 := by 
  have h1 : {x | x ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 x).length = 3 ∧ (Nat.digits 10 x).toFinset = {9, 8, 7}} = Finset.filter (fun x => (Nat.digits 10 x).length = 3 ∧ (Nat.digits 10 x).toFinset = {9, 8, 7}) (Finset.Icc 100 999) := by
    ext n
    simp 
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide