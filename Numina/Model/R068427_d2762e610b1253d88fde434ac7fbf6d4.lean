import Mathlib

theorem algebra_18933 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).sum = 7} = 7 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).sum = 7} = 
          (Finset.filter (fun n => (Nat.digits 10 n).sum = 7) (Finset.Icc 10 99)) := by
    ext n
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide