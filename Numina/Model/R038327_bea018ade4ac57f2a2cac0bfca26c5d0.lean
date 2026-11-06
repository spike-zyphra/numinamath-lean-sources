import Mathlib

theorem number_theory_222844 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 1000000 ∧ Even n ∧ Odd (Nat.digits 10 n).sum} >
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 1000000 ∧ Odd n ∧ Even (Nat.digits 10 n).sum} := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 1000000 ∧ Even n ∧ Odd (Nat.digits 10 n).sum} = Finset.filter (fun n => Even n ∧ Odd (Nat.digits 10 n).sum) (Finset.Icc 1 1000000) := by
    ext n
    simp
    <;> aesop
  have h2 : {n : ℕ | n ∈ Finset.Icc 1 1000000 ∧ Odd n ∧ Even (Nat.digits 10 n).sum} = Finset.filter (fun n => Odd n ∧ Even (Nat.digits 10 n).sum) (Finset.Icc 1 1000000) := by
    ext n
    simp
    <;> aesop
  rw [h1, h2]
  rw [Set.ncard_coe_Finset, Set.ncard_coe_Finset]
  native_decide