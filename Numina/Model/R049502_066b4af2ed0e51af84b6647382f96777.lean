import Mathlib

theorem number_theory_120280 :
    {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).all (fun d => d % 2 = (Nat.digits 10 n).headI % 2)}.ncard =
    {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).headI % 2 ≠ (Nat.digits 10 n).tail.headI % 2}.ncard := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).all (fun d => d % 2 = (Nat.digits 10 n).headI % 2)} = Finset.filter (fun n => (Nat.digits 10 n).all (fun d => d % 2 = (Nat.digits 10 n).headI % 2)) (Finset.Icc 10 99) := by 
    ext n 
    simp 
    <;> try tauto 
  have h2 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).headI % 2 ≠ (Nat.digits 10 n).tail.headI % 2} = Finset.filter (fun n => (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).headI % 2 ≠ (Nat.digits 10 n).tail.headI % 2) (Finset.Icc 10 99) := by 
    ext n 
    simp 
    <;> try tauto 
  rw [h1, h2]
  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]
  native_decide