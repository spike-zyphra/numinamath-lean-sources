import Mathlib

theorem number_theory_207550 :
    Set.ncard {x | x ∈ Finset.Icc 1 56000 ∧ 7 ∣ x ∧ ¬8 ∣ x} =
    Set.ncard {x | x ∈ Finset.Icc 1 56000 ∧ 8 ∣ x} := by 
  have h₁ : {x | x ∈ Finset.Icc 1 56000 ∧ 7 ∣ x ∧ ¬8 ∣ x} = Finset.filter (fun x => 7 ∣ x ∧ ¬8 ∣ x) (Finset.Icc 1 56000) := by 
    ext x
    simp 
  rw [h₁]
  have h₂ : {x | x ∈ Finset.Icc 1 56000 ∧ 8 ∣ x} = Finset.filter (fun x => 8 ∣ x) (Finset.Icc 1 56000) := by 
    ext x
    simp 
  rw [h₂]
  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]
  native_decide