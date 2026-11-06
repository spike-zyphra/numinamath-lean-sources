import Mathlib

theorem number_theory_135346 :
    {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Even n ∨ n % 3 = 0) ∧ ¬(Even n ∧ n % 3 = 0) ∧
      (3 ∣ n ∨ n % 10 = 5) ∧ ¬(3 ∣ n ∧ n % 10 = 5) ∧ (5 ∣ n ∨ (Nat.digits 10 n).sum = 12) ∧
      ¬(5 ∣ n ∧ (Nat.digits 10 n).sum = 12)}.ncard = 3 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Even n ∨ n % 3 = 0) ∧ ¬(Even n ∧ n % 3 = 0) ∧
      (3 ∣ n ∨ n % 10 = 5) ∧ ¬(3 ∣ n ∧ n % 10 = 5) ∧ (5 ∣ n ∨ (Nat.digits 10 n).sum = 12) ∧
      ¬(5 ∣ n ∧ (Nat.digits 10 n).sum = 12)} = Finset.filter (fun n => (Even n ∨ n % 3 = 0) ∧ ¬(Even n ∧ n % 3 = 0) ∧
      (3 ∣ n ∨ n % 10 = 5) ∧ ¬(3 ∣ n ∧ n % 10 = 5) ∧ (5 ∣ n ∨ (Nat.digits 10 n).sum = 12) ∧
      ¬(5 ∣ n ∧ (Nat.digits 10 n).sum = 12)) (Finset.Icc 10 99) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide