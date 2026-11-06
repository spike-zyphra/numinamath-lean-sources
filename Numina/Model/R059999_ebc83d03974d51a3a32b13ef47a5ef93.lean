import Mathlib

theorem number_theory_233184 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).sum = 9} = 9 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).sum = 9} = Finset.filter (fun n : ℕ => (Nat.digits 10 n).sum = 9) (Finset.Icc 10 99) := by 
    ext n 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide