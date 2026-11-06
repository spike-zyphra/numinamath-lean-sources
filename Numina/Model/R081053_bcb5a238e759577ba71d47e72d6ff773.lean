import Mathlib

theorem number_theory_10798 : {x | x ∈ Finset.Icc 1 2009 ∧ ¬(3 ∣ x) ∧ ¬(5 ∣ x)}.ncard = 1072 := by 
  have h1 : {x | x ∈ Finset.Icc 1 2009 ∧ ¬(3 ∣ x) ∧ ¬(5 ∣ x)} = Finset.filter (fun x => ¬(3 ∣ x) ∧ ¬(5 ∣ x)) (Finset.Icc 1 2009) := by 
    ext x
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide