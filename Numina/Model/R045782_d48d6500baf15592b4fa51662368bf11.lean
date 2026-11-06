import Mathlib

theorem number_theory_32040 : {x | x ∈ Finset.Icc 1 365 ∧ ¬(x % 3 = 0 ∨ x % 4 = 0 ∨ x % 5 = 0)}.ncard = 146 := by
  have h1 : {x | x ∈ Finset.Icc 1 365 ∧ ¬(x % 3 = 0 ∨ x % 4 = 0 ∨ x % 5 = 0)} = Finset.filter (fun x => ¬(x % 3 = 0 ∨ x % 4 = 0 ∨ x % 5 = 0)) (Finset.Icc 1 365) := by 
    ext x
    simp 
    <;> aesop
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide