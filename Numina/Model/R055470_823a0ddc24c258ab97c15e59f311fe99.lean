import Mathlib

theorem number_theory_96421 :
    {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 43 ∧ 11 ∣ n}.ncard / {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 43}.ncard = 1 / 5 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 43 ∧ 11 ∣ n} = Finset.filter (fun n => (Nat.digits 10 n).sum = 43 ∧ 11 ∣ n) (Finset.Icc 10000 99999) := by
    ext n 
    simp 
  have h2 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 43} = Finset.filter (fun n => (Nat.digits 10 n).sum = 43) (Finset.Icc 10000 99999) := by 
    ext n 
    simp 
  rw [h1] 
  rw [h2] 
  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]
  native_decide