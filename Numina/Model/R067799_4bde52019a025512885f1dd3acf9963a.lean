import Mathlib

theorem number_theory_6891 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % (Nat.digits 10 n).headI = 0 ∧ n % (Nat.digits 10 n).tail.headI = 0} = 14 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % (Nat.digits 10 n).headI = 0 ∧ n % (Nat.digits 10 n).tail.headI = 0} = Finset.filter (fun n => n % (Nat.digits 10 n).headI = 0 ∧ n % (Nat.digits 10 n).tail.headI = 0) (Finset.Icc 10 99) := by 
    ext n
    simp 
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide