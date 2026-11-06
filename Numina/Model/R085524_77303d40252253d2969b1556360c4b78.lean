import Mathlib

theorem number_theory_95638 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (n - (Nat.digits 10 n).sum) % 10 = 6} = 10 := by 
  have h : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (n - (Nat.digits 10 n).sum) % 10 = 6} = 
      Finset.filter (fun (n : ℕ) => (n - (Nat.digits 10 n).sum) % 10 = 6) (Finset.Icc 10 99) := by 
    ext n 
    simp 
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide