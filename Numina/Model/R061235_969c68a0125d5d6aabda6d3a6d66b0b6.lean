import Mathlib

theorem number_theory_597 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ n % 11 = 8 ∧ (Nat.digits 10 n).contains 1 ∧ (Nat.digits 10 n).contains 9 ∧ (Nat.digits 10 n).count 8 = 2} = 4 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ n % 11 = 8 ∧ (Nat.digits 10 n).contains 1 ∧ (Nat.digits 10 n).contains 9 ∧ (Nat.digits 10 n).count 8 = 2} = Finset.filter (fun n => n % 11 = 8 ∧ (Nat.digits 10 n).contains 1 ∧ (Nat.digits 10 n).contains 9 ∧ (Nat.digits 10 n).count 8 = 2) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide