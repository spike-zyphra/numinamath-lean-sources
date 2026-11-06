import Mathlib

theorem number_theory_237534 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 50 ∧ x % 3 = 1} = 17 := by 
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 50 ∧ x % 3 = 1} = 
          Finset.filter (fun x => x % 3 = 1) (Finset.Icc 1 50) := by 
    ext x
    simp 
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  <;> native_decide