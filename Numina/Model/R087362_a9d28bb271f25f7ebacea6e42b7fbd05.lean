import Mathlib

theorem algebra_21219 : {x | x ∈ Finset.Icc 0 (7 * 60) ∧ (x % 2 = 0 ∧ x % 3 = 0 ∧ x % 5 = 0)}.ncard = 15 := by
  have h1 : {x | x ∈ Finset.Icc 0 (7 * 60) ∧ (x % 2 = 0 ∧ x % 3 = 0 ∧ x % 5 = 0)} = Finset.filter (fun x => x % 2 = 0 ∧ x % 3 = 0 ∧ x % 5 = 0) (Finset.Icc 0 (7 * 60)) := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide