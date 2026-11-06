import Mathlib

theorem number_theory_200066 :
    Set.ncard {n : ℕ | Odd n ∧ n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 11 ∧ (Nat.digits 10 (n % 100)).sum = 5} = 18 := by
  have h1 : {n : ℕ | Odd n ∧ n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 11 ∧ (Nat.digits 10 (n % 100)).sum = 5} = Finset.filter (fun n => Odd n ∧ (Nat.digits 10 n).sum = 11 ∧ (Nat.digits 10 (n % 100)).sum = 5) (Finset.Icc 1000 9999) := by
    ext n
    simp [Finset.mem_Icc, Nat.odd_iff]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide