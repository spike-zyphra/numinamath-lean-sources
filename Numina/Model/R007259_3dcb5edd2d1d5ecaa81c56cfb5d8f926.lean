import Mathlib

theorem number_theory_227555 :
    {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ n ∧ (Nat.digits 10 n).headI > (Nat.digits 10 n).tail.headI}.ncard * 100 +
    {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ n ∧ (Nat.digits 10 n).headI < (Nat.digits 10 n).tail.headI}.ncard = 413 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ n ∧ (Nat.digits 10 n).headI > (Nat.digits 10 n).tail.headI} = 
    Finset.filter (fun n => 5 ∣ n ∧ (Nat.digits 10 n).headI > (Nat.digits 10 n).tail.headI) (Finset.Icc 10 99) := by
    ext n
    simp
  have h2 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ n ∧ (Nat.digits 10 n).headI < (Nat.digits 10 n).tail.headI} = 
    Finset.filter (fun n => 5 ∣ n ∧ (Nat.digits 10 n).headI < (Nat.digits 10 n).tail.headI) (Finset.Icc 10 99) := by
    ext n
    simp
  rw [h1, h2]
  rw [Set.ncard_coe_Finset, Set.ncard_coe_Finset]
  native_decide