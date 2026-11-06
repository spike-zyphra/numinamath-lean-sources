import Mathlib

theorem number_theory_317654 :
    {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 36 ∧ Even n}.ncard >
    {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 38 ∧ Odd n}.ncard := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 36 ∧ Even n} = Finset.filter (fun n => (Nat.digits 10 n).sum = 36 ∧ Even n) (Finset.Icc 10000 99999) := by
    ext n
    simp
  have h2 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ (Nat.digits 10 n).sum = 38 ∧ Odd n} = Finset.filter (fun n => (Nat.digits 10 n).sum = 38 ∧ Odd n) (Finset.Icc 10000 99999) := by
    ext n 
    simp
  rw [h1, h2]
  rw [Set.ncard_coe_Finset, Set.ncard_coe_Finset]
  native_decide