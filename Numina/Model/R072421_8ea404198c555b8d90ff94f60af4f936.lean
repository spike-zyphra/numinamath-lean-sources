import Mathlib

theorem number_theory_176300 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).headI + (Nat.digits 10 n).tail.headI = 8} = 8 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).headI + (Nat.digits 10 n).tail.headI = 8} = Finset.filter (fun (n : ℕ) => (Nat.digits 10 n).headI + (Nat.digits 10 n).tail.headI = 8) (Finset.Icc 10 99) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide