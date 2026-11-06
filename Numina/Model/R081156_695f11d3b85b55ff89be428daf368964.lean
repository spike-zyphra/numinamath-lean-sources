import Mathlib

theorem number_theory_254897 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % (Nat.digits 10 n).sum = 0} = 23 := by
  have : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % (Nat.digits 10 n).sum = 0} = Finset.filter (fun n => n % (Nat.digits 10 n).sum = 0) (Finset.Icc 10 99) := by 
    ext n
    simp 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide